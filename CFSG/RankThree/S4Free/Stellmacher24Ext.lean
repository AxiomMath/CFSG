module

public import CFSG.RankThree.S4Free.StellmacherL24
public import CFSG.Blueprint.Catalog
import CFSG.LieType.Ree.SuzukiSimple
import TauCeti.Algebra.Group.Subgroup.ModularLaw

public section

universe u

namespace CFSG.RankThree.S4Free.Stell

open Subgroup
open scoped commutatorElement

section Elementary

variable {G : Type*} [Group G]

theorem eq_one_of_sq_eq_one_of_odd {K : Subgroup G} (hK : ¬ 2 ∣ Nat.card K) {g : G}
    (hg : g ∈ K) (h2 : g ^ 2 = 1) : g = 1 := by
  have h1 : orderOf (⟨g, hg⟩ : K) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using h2))
  have hc : Nat.Coprime 2 (Nat.card K) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hK
  have h4 := Nat.eq_one_of_dvd_coprimes hc h1 (orderOf_dvd_natCard _)
  exact congrArg Subtype.val (orderOf_eq_one_iff.mp h4)

theorem commutator_le_zpowers_mul {s t : G} (hs : s * s = 1) (ht : t * t = 1)
    (hst : zpowers s ⊔ zpowers t = ⊤) : commutator G ≤ zpowers (s * t) := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hinv : (s * t)⁻¹ = t * s := by rw [mul_inv_rev, hsi, hti]
  have hnorm : (zpowers (s * t)).Normal := by
    rw [← normalizer_eq_top_iff, eq_top_iff, ← hst]
    refine sup_le (zpowers_le_normalizer_of_inv hs ?_) (zpowers_le_normalizer_of_inv ht ?_)
    · rw [hinv, hsi, show s * (s * t) * s = s * s * t * s by group, hs, one_mul]
    · rw [hinv, hti, show t * (s * t) * t = t * s * (t * t) by group, ht, mul_one]
  have hq : ∀ g : G, (g : G ⧸ zpowers (s * t)) ∈ zpowers (s : G ⧸ zpowers (s * t)) := by
    have ht' : (t : G ⧸ zpowers (s * t)) = (s : G ⧸ zpowers (s * t))⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, ← hinv]
      exact inv_mem (mem_zpowers _)
    have hle : (⊤ : Subgroup G) ≤ (zpowers (s : G ⧸ zpowers (s * t))).comap
        (QuotientGroup.mk' (zpowers (s * t))) := by
      rw [← hst]
      refine sup_le (zpowers_le.mpr (mem_zpowers _)) (zpowers_le.mpr ?_)
      change (t : G ⧸ zpowers (s * t)) ∈ zpowers (s : G ⧸ zpowers (s * t))
      rw [ht']
      exact inv_mem (mem_zpowers _)
    exact fun g => hle (mem_top g)
  rw [_root_.commutator_def, commutator_le]
  intro g _ h _
  have hcomm : Commute (g : G ⧸ zpowers (s * t)) (h : G ⧸ zpowers (s * t)) := by
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp (hq g)
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (hq h)
    rw [← hi, ← hj]
    exact Commute.zpow_zpow_self _ i j
  have h1 : QuotientGroup.mk' (zpowers (s * t)) ⁅g, h⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact hcomm
  exact (QuotientGroup.eq_one_iff _).mp h1

end Elementary

@[expose] def SzOverOTwo (X : Type*) [Group X] : Prop :=
  ∃ (R : Subgroup X) (_ : R.Normal), oTwo X ≤ R ∧ ¬ 2 ∣ (oTwo X).relIndex R ∧
    ∃ a : ℕ, 1 ≤ a ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ (2 * a + 1) ∧
      Nonempty (X ⧸ R ≃* CFSG.Blueprint.suzukiGroup a K)

section SzOverOTwo

variable {X Y : Type*} [Group X] [Group Y]

theorem SzOverOTwo.of_surjective [Finite X] (f : X →* Y) (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) (h : SzOverOTwo Y) : SzOverOTwo X := by
  obtain ⟨R, hRn, hOR, hodd, a, ha, K, _, _, hK, ⟨e⟩⟩ := h
  have hO : (oTwo Y).comap f = oTwo X := comap_oTwo_eq f hf hker
  have hφ : Function.Surjective ((QuotientGroup.mk' R).comp f) :=
    (QuotientGroup.mk'_surjective R).comp hf
  have hkerφ : R.comap f = ((QuotientGroup.mk' R).comp f).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  refine ⟨R.comap f, inferInstance, ?_, ?_, a, ha, K, inferInstance, inferInstance, hK, ⟨?_⟩⟩
  · rw [← hO]
    exact comap_mono hOR
  · rwa [← hO, relIndex_comap, map_comap_eq_self_of_surjective hf]
  · exact (QuotientGroup.quotientMulEquivOfEq hkerφ).trans
      ((QuotientGroup.quotientKerEquivOfSurjective _ hφ).trans e)

theorem SzOverOTwo.of_mulEquiv [Finite X] (e : X ≃* Y) (h : SzOverOTwo Y) : SzOverOTwo X := by
  refine h.of_surjective e.toMonoidHom e.surjective ?_
  have : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e.injective
  rw [this]
  exact IsPGroup.of_bot

theorem SzOverOTwo.of_surjective_odd [Finite X] (f : X →* Y) (hf : Function.Surjective f)
    (hker : ¬ 2 ∣ Nat.card f.ker) (hX : oTwo X = ⊥) (hY : oTwo Y = ⊥) (h : SzOverOTwo Y) :
    SzOverOTwo X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hRn, -, hodd, a, ha, K, _, _, hK, ⟨e⟩⟩ := h
  rw [hY, relIndex_bot_left] at hodd
  have hφ : Function.Surjective ((QuotientGroup.mk' R).comp f) :=
    (QuotientGroup.mk'_surjective R).comp hf
  have hkerφ : R.comap f = ((QuotientGroup.mk' R).comp f).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  refine ⟨R.comap f, inferInstance, by rw [hX]; exact bot_le, ?_, a, ha, K, inferInstance,
    inferInstance, hK, ⟨?_⟩⟩
  · rw [hX, relIndex_bot_left]
    intro h2
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := R.comap f) 2 h2
    have hx2 : (x : X) ^ 2 = 1 := by
      have := pow_orderOf_eq_one x
      rw [hx] at this
      simpa using congrArg Subtype.val this
    have hfx : f x = 1 := eq_one_of_sq_eq_one_of_odd hodd x.2 (by rw [← map_pow, hx2, map_one])
    have hx1 : (x : X) = 1 := eq_one_of_sq_eq_one_of_odd hker hfx hx2
    have : x = 1 := Subtype.ext hx1
    rw [this, orderOf_one] at hx
    exact absurd hx (by norm_num)
  · exact (QuotientGroup.quotientMulEquivOfEq hkerφ).trans
      ((QuotientGroup.quotientKerEquivOfSurjective _ hφ).trans e)

end SzOverOTwo

section Statement

variable {H : Type*} [Group H] {S M A L K : Subgroup H}

structure IsL24Core (S M A L : Subgroup H) : Prop where
  le : A ≤ L
  not_le : ¬ L ≤ M
  not_dvd_relIndex : ¬ 2 ∣ S.relIndex L
  sup_conj : ∀ x ∈ L, x ∉ M → A ⊔ A.map (MulAut.conj x).toMonoidHom = L

structure IsL24Sz (S M A L : Subgroup H) : Prop extends IsL24Core S M A L where
  suzuki : SzOverOTwo ↥L

theorem IsL24.toCore (h : IsL24 S M A L) : IsL24Core S M A L :=
  ⟨h.le, h.not_le, h.not_dvd_relIndex, h.sup_conj⟩

theorem IsL24Core.eq_of_le (h : IsL24Core S M A L) (hKL : K ≤ L) (hAK : A ≤ K)
    (hKM : ¬ K ≤ M) : K = L := by
  obtain ⟨x, hxK, hxM⟩ := Set.not_subset.mp hKM
  refine le_antisymm hKL ?_
  rw [← h.sup_conj x (hKL hxK) hxM]
  exact sup_le hAK (map_conj_le hAK hxK)

theorem IsL24Core.oTwo_le [Finite H] (h : IsL24Core S M A L) (hS : IsPGroup 2 S) (hSM : S ≤ M) :
    (oTwo ↥L).map L.subtype ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (S.subgroupOf L) := hS.comap_subtype
  have hle : oTwo ↥L ≤ S.subgroupOf L := by
    have h1 := (oTwo_isPGroup ↥L).le_sylow_of_normal
      (hP.toSylow (show ¬ 2 ∣ (S.subgroupOf L).index from h.not_dvd_relIndex))
    rwa [IsPGroup.toSylow_coe] at h1
  calc (oTwo ↥L).map L.subtype ≤ (S.subgroupOf L).map L.subtype := map_mono hle
    _ = S ⊓ L := subgroupOf_map_subtype S L
    _ ≤ M := inf_le_left.trans hSM

theorem IsL24Core.map_subtype {U : Subgroup H} (hAU : A ≤ U) {L' : Subgroup U}
    (h : IsL24Core (S.subgroupOf U) (M.subgroupOf U) (A.subgroupOf U) L') :
    IsL24Core S M A (L'.map U.subtype) where
  le := fun a ha => ⟨⟨a, hAU ha⟩, h.le (by simpa [mem_subgroupOf] using ha), rfl⟩
  not_le := by
    intro hle
    apply h.not_le
    intro x hx
    rw [mem_subgroupOf]
    exact hle ⟨x, hx, rfl⟩
  not_dvd_relIndex := by
    have hL : (L'.map U.subtype).subgroupOf U = L' :=
      comap_map_eq_self_of_injective U.subtype_injective L'
    rw [← relIndex_subgroupOf (map_subtype_le L'), hL]
    exact h.not_dvd_relIndex
  sup_conj := by
    rintro _ ⟨x, hx, rfl⟩ hxM
    have hxM' : x ∉ M.subgroupOf U := by rwa [mem_subgroupOf]
    have := congrArg (Subgroup.map U.subtype) (h.sup_conj x hx hxM')
    rwa [Subgroup.map_sup, map_map_conj, subgroupOf_map_subtype, inf_of_le_left hAU] at this

theorem IsL24Sz.map_subtype [Finite H] {U : Subgroup H} (hAU : A ≤ U) {L' : Subgroup U}
    (h : IsL24Sz (S.subgroupOf U) (M.subgroupOf U) (A.subgroupOf U) L') :
    IsL24Sz S M A (L'.map U.subtype) :=
  ⟨h.toIsL24Core.map_subtype hAU,
    h.suzuki.of_mulEquiv (L'.equivMapOfInjective U.subtype U.subtype_injective).symm⟩

theorem card_map_subgroupOf_eq_relIndex [Finite H] (hAL : A ≤ L)
    (hA : CFSG.Open.IsElemAbelian 2 A) {R : Subgroup L} [R.Normal] (hOR : oTwo ↥L ≤ R)
    (hodd : ¬ 2 ∣ (oTwo ↥L).relIndex R) {G : Type*} [Group G] (φ : ↥L →* G)
    (hker : φ.ker = R) :
    Nat.card ((A.subgroupOf L).map φ) = ((oTwo ↥L).map L.subtype).relIndex A := by
  have hAR : R ⊓ A.subgroupOf L ≤ oTwo ↥L := by
    rintro g ⟨hgR, hgA⟩
    set ψ := QuotientGroup.mk' (oTwo ↥L) with hψ
    have hcard : ¬ 2 ∣ Nat.card (R.map ψ) := by
      rwa [← relIndex_ker, hψ, QuotientGroup.ker_mk']
    have hg2 : g ^ 2 = 1 := Subtype.ext (by simpa using hA.2 _ hgA)
    have h1 : ψ g = 1 :=
      eq_one_of_sq_eq_one_of_odd hcard (mem_map_of_mem ψ hgR) (by rw [← map_pow, hg2, map_one])
    rwa [hψ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hsub : ((oTwo ↥L).map L.subtype).subgroupOf L = oTwo ↥L :=
    comap_map_eq_self_of_injective L.subtype_injective _
  rw [← relIndex_ker, hker, ← inf_relIndex_right,
    le_antisymm (le_inf hAR inf_le_right) (inf_le_inf_right (A.subgroupOf L) hOR),
    inf_relIndex_right, ← relIndex_subgroupOf hAL, hsub]

theorem IsL24Sz.four_le [Finite H] (h : IsL24Sz S M A L)
    (hA : CFSG.Open.IsElemAbelian 2 A) : 4 ≤ ((oTwo ↥L).map L.subtype).relIndex A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hRn, hOR, hodd, a, ha, K, _, _, hK, ⟨e⟩⟩ := h.suzuki
  set φ : ↥L →* CFSG.Blueprint.suzukiGroup a K := e.toMonoidHom.comp (QuotientGroup.mk' R)
    with hφ
  have hφs : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective R)
  have hker : φ.ker = R := by
    ext g
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  set A' := A.subgroupOf L with hA'
  have hcardA : Nat.card (A'.map φ) = ((oTwo ↥L).map L.subtype).relIndex A :=
    card_map_subgroupOf_eq_relIndex h.le hA hOR hodd φ hker
  have hsq : ∀ g ∈ A'.map φ, g * g = 1 := by
    rintro _ ⟨g, hg, rfl⟩
    have : g ^ 2 = 1 := Subtype.ext (by simpa using hA.2 _ hg)
    rw [← map_mul, ← pow_two, this, map_one]
  have hA2 : IsPGroup 2 ↥(A'.map φ) := fun g =>
    ⟨1, Subtype.ext (by simpa [pow_one, pow_two] using hsq g g.2)⟩
  by_contra hlt
  push Not at hlt
  rw [← hcardA] at hlt
  have hle2 : Nat.card (A'.map φ) ≤ 2 := by
    obtain ⟨k, hk⟩ := hA2.exists_card_eq
    rw [hk] at hlt ⊢
    rcases k with _ | _ | k
    · norm_num
    · norm_num
    · exfalso
      rw [pow_succ, pow_succ] at hlt
      have := Nat.one_le_two_pow (n := k)
      omega
  obtain ⟨s, hs, hAs⟩ : ∃ s : CFSG.Blueprint.suzukiGroup a K, s * s = 1 ∧ A'.map φ ≤ zpowers s := by
    by_cases hbot : A'.map φ = ⊥
    · exact ⟨1, mul_one 1, hbot ▸ bot_le⟩
    · obtain ⟨⟨s, hsA⟩, hs1⟩ := ne_bot_iff_exists_ne_one.mp hbot
      have hs1' : s ≠ 1 := fun h' => hs1 (Subtype.ext h')
      refine ⟨s, hsq s hsA, ?_⟩
      have h2 : Nat.card (zpowers s) = 2 := by
        rw [Nat.card_zpowers]
        exact orderOf_eq_prime (by rw [pow_two]; exact hsq s hsA) hs1'
      exact (eq_of_le_of_card_ge (zpowers_le.mpr hsA) (h2 ▸ hle2)).ge
  obtain ⟨x, hxL, hxM⟩ := Set.not_subset.mp h.not_le
  set x' : ↥L := ⟨x, hxL⟩ with hx'
  have hsup' : A' ⊔ A'.map (MulAut.conj x').toMonoidHom = ⊤ := by
    apply map_injective L.subtype_injective
    rw [Subgroup.map_sup, map_map_conj, subgroupOf_map_subtype, inf_of_le_left h.le,
      ← MonoidHom.range_eq_map, range_subtype]
    exact h.sup_conj x hxL hxM
  set y := φ x' with hy
  have htt : (y * s * y⁻¹) * (y * s * y⁻¹) = 1 := by
    rw [show y * s * y⁻¹ * (y * s * y⁻¹) = y * (s * s) * y⁻¹ by group, hs, mul_one,
      mul_inv_cancel]
  have htop : zpowers s ⊔ zpowers (y * s * y⁻¹) = ⊤ := by
    rw [eq_top_iff]
    have h1 : (A' ⊔ A'.map (MulAut.conj x').toMonoidHom).map φ = ⊤ := by
      rw [hsup', map_top_of_surjective φ hφs]
    rw [← h1, Subgroup.map_sup, map_map_conj]
    refine sup_le_sup hAs ?_
    calc ((A'.map φ).map (MulAut.conj (φ x')).toMonoidHom)
        ≤ (zpowers s).map (MulAut.conj (φ x')).toMonoidHom := map_mono hAs
      _ = zpowers (y * s * y⁻¹) := by rw [MonoidHom.map_zpowers]; rfl
  have hcl := commutator_le_zpowers_mul hs htt htop
  rw [(CFSG.LieType.Ree.suzuki_perfect ha hK).1] at hcl
  have hcomm : ∀ g g' : CFSG.Blueprint.suzukiGroup a K, g * g' = g' * g := by
    intro g g'
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp (hcl (mem_top g))
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp (hcl (mem_top g'))
    exact (Commute.zpow_zpow_self _ i j).eq
  have hbot : commutator (CFSG.Blueprint.suzukiGroup a K) = ⊥ := by
    rw [_root_.commutator_def, commutator_eq_bot_iff_le_centralizer]
    intro g _
    rw [mem_centralizer_iff]
    intro g' _
    exact hcomm g' g
  obtain ⟨-, hnt, -⟩ := CFSG.LieType.Ree.suzuki_simple ha hK
  obtain ⟨w, hw⟩ := exists_ne (1 : CFSG.Blueprint.suzukiGroup a K)
  have hw' : w ∈ (⊥ : Subgroup (CFSG.Blueprint.suzukiGroup a K)) := by
    rw [← hbot, (CFSG.LieType.Ree.suzuki_perfect ha hK).1]
    exact mem_top w
  exact hw (mem_bot.mp hw')

end Statement

@[expose] def IH24Of (P : ∀ (G : Type u) [Group G], Prop) (n : ℕ) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], P G → Nat.card G < n →
    ∀ {S M A : Subgroup G}, Hyp24 S M A → ∃ L, IsL24 S M A L ∨ IsL24Sz S M A L

@[expose] def Step24 (P : ∀ (G : Type u) [Group G], Prop) : Prop :=
  ∀ (H : Type u) [Group H] [Finite H] {S M A : Subgroup H}, P H → Hyp24 S M A → oTwo H = ⊥ →
    M.normalCore = ⊥ → ∀ N : Subgroup H, N.Normal → N ≠ ⊥ →
      (∀ K : Subgroup H, K.Normal → K ≤ N → K = ⊥ ∨ K = N) → ¬ Group.IsSolvable N →
        ∃ L, IsL24 S M A L ∨ IsL24Sz S M A L

section Steps

variable {P : ∀ (G : Type u) [Group G], Prop} {H : Type u} [Group H] [Finite H]
  {S M A : Subgroup H}

theorem exists_isL24_or_isL24Sz_of_oTwo_ne_bot (hPq : P (H ⧸ oTwo H)) (ih : IH24Of P (Nat.card H))
    (h : Hyp24 S M A) (hO : oTwo H ≠ ⊥) : ∃ L, IsL24 S M A L ∨ IsL24Sz S M A L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := oTwo H with hOdef
  set π := QuotientGroup.mk' O with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hker : π.ker = O := QuotientGroup.ker_mk' O
  have hOS : O ≤ S := by
    have := (oTwo_isPGroup H).le_sylow_of_normal (h.isPGroup.toSylow h.not_dvd_index)
    simpa using this
  have hOM : O ≤ M := hOS.trans h.le_M
  have hcard : Nat.card (H ⧸ O) < Nat.card H := by
    rw [card_eq_card_quotient_mul_card_subgroup O]
    have h1 : 1 < Nat.card O := (one_lt_card_iff_ne_bot O).mpr hO
    have h2 := Nat.card_pos (α := H ⧸ O)
    nlinarith
  obtain ⟨Lb, hLb⟩ := ih (H ⧸ O) hPq hcard (h.map_quotient O hOM)
  have hLbc : IsL24Core (S.map π) (M.map π) (A.map π) Lb := hLb.elim IsL24.toCore (·.toIsL24Core)
  have hcM : (M.map π).comap π = M := by rw [comap_map_eq, hker, sup_of_le_left hOM]
  have hnotM : ∀ x, x ∉ M → π x ∉ M.map π := fun x hx hxM => hx (by rw [← hcM]; exact hxM)
  set L₁ := Lb.comap π with hL₁
  obtain ⟨L, ⟨hAL, hLL₁, hLM⟩, hmin⟩ := exists_minimal_subgroup
    (fun K => A ≤ K ∧ K ≤ L₁ ∧ ¬ K ≤ M)
    ⟨L₁, map_le_iff_le_comap.mp hLbc.le, le_rfl, fun hle => hLbc.not_le (by
      rw [← map_comap_eq_self_of_surjective hπs Lb]
      exact map_mono hle)⟩
  have hLmap : L.map π = Lb :=
    hLbc.eq_of_le (map_le_iff_le_comap.mpr hLL₁) (map_mono hAL) fun hle => hLM (by
      rw [← hcM]
      exact map_le_iff_le_comap.mp hle)
  have hcore : IsL24Core S M A L := by
    refine ⟨hAL, hLM, ?_, ?_⟩
    · rw [← relIndex_map_of_ker_le π (by rw [hker]; exact hOS), hLmap]
      exact hLbc.not_dvd_relIndex
    · intro x hxL hxM
      refine hmin _ ⟨le_sup_left, sup_le hAL (map_conj_le hAL hxL) |>.trans hLL₁, ?_⟩
        (sup_le hAL (map_conj_le hAL hxL))
      intro hle
      apply hLbc.not_le
      rw [← hLbc.sup_conj (π x) (hLL₁ hxL) (hnotM x hxM), ← map_map_conj, ← Subgroup.map_sup]
      exact map_mono hle
  have hfker : (π.subgroupMap L).ker = O.comap L.subtype := by
    ext x
    rw [MonoidHom.mem_ker, mem_comap, coe_subtype]
    have key : π.subgroupMap L x = 1 ↔ π (x : H) = 1 := by
      constructor
      · intro hx
        simpa using congrArg Subtype.val hx
      · intro hx
        exact Subtype.ext (by simpa using hx)
    rw [key, hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hk2 : IsPGroup 2 (π.subgroupMap L).ker := by
    rw [hfker]
    exact (oTwo_isPGroup H).comap_subtype
  rcases hLb with hLb | hLb
  · refine ⟨L, Or.inl ⟨hcore.le, hcore.not_le, hcore.not_dvd_relIndex, hcore.sup_conj, ?_⟩⟩
    obtain ⟨r, s, hr, hr2, hs, ⟨e⟩⟩ := hLb.dihedral
    obtain ⟨e₁⟩ := nonempty_quotient_oTwo_mulEquiv (π.subgroupMap L)
      (π.subgroupMap_surjective L) hk2
    obtain ⟨e₂⟩ := nonempty_quotient_oTwo_mulEquiv_of_mulEquiv (MulEquiv.subgroupCongr hLmap)
    exact ⟨r, s, hr, hr2, hs, ⟨e₁.trans (e₂.trans e)⟩⟩
  · exact ⟨L, Or.inr ⟨hcore, (hLb.suzuki.of_mulEquiv (MulEquiv.subgroupCongr hLmap)).of_surjective
      (π.subgroupMap L) (π.subgroupMap_surjective L) hk2⟩⟩

theorem exists_isL24_or_isL24Sz_of_sup_normalCore {U : Subgroup H} (hPU : P U)
    (ih : IH24Of P (Nat.card H)) (h : Hyp24 S M A) (hSU : S ≤ U) (hUD : U ⊔ M.normalCore = ⊤)
    (hU : U ≠ ⊤) : ∃ L, IsL24 S M A L ∨ IsL24Sz S M A L := by
  set D := M.normalCore with hDdef
  have hDM : D ≤ M := normalCore_le M
  have hAU : A ≤ U := h.le_S.trans hSU
  have hdec : ∀ g : H, ∃ d ∈ D, ∃ u ∈ U, g = d * u := by
    intro g
    have hg : g ∈ ((D ⊔ U : Subgroup H) : Set H) := by
      rw [SetLike.mem_coe, sup_comm, hUD]
      exact mem_top g
    rw [normal_mul D U] at hg
    obtain ⟨d, hd, u, hu, rfl⟩ := hg
    exact ⟨d, hd, u, hu, rfl⟩
  have hcoatom : IsCoatom (M.subgroupOf U) := by
    refine ⟨fun htop => h.isCoatom.1 ?_, fun K hK => ?_⟩
    · rw [eq_top_iff, ← hUD]
      refine sup_le (fun u hu => ?_) hDM
      have : (⟨u, hu⟩ : U) ∈ M.subgroupOf U := by
        rw [htop]
        exact mem_top _
      exact this
    · obtain ⟨k, hkK, hkM⟩ := SetLike.exists_of_lt hK
      have hKD : K.map U.subtype ⊔ D = ⊤ := by
        apply h.isCoatom.2
        refine lt_of_le_of_ne (fun m hm => ?_) fun heq => hkM ?_
        · obtain ⟨d, hd, u', hu', rfl⟩ := hdec m
          have hu'M : u' ∈ M := by
            have := M.mul_mem (M.inv_mem (hDM hd)) hm
            rwa [inv_mul_cancel_left] at this
          have hu'K : (⟨u', hu'⟩ : U) ∈ K := hK.le (by rw [mem_subgroupOf]; exact hu'M)
          rw [sup_comm]
          exact mul_mem_sup hd ⟨_, hu'K, rfl⟩
        · rw [mem_subgroupOf, heq]
          exact mem_sup_left ⟨k, hkK, rfl⟩
      rw [eq_top_iff]
      rintro ⟨u, hu⟩ -
      have hg : u ∈ ((K.map U.subtype ⊔ D : Subgroup H) : Set H) := by
        rw [SetLike.mem_coe, hKD]
        exact mem_top u
      rw [mul_normal] at hg
      obtain ⟨_, ⟨k', hk', rfl⟩, d, hd, hkd⟩ := hg
      have hkd : (k' : H) * d = u := hkd
      have hdU : d ∈ U := by
        have := U.mul_mem (U.inv_mem k'.2) hu
        rwa [← hkd, inv_mul_cancel_left] at this
      have hdK : (⟨d, hdU⟩ : U) ∈ K := hK.le (by rw [mem_subgroupOf]; exact hDM hd)
      have : (⟨u, hu⟩ : U) = k' * ⟨d, hdU⟩ := Subtype.ext hkd.symm
      rw [this]
      exact K.mul_mem hk' hdK
  have hcore : ¬ A.subgroupOf U ≤ (M.subgroupOf U).normalCore := by
    intro hle
    apply h.not_le_normalCore
    intro a ha
    rw [mem_normalCore_iff]
    intro g
    obtain ⟨d, hd, u, hu, rfl⟩ := hdec g
    have h1 : u * a * u⁻¹ ∈ M := by
      have := mem_normalCore_iff.mp
        (hle (show (⟨a, hAU ha⟩ : U) ∈ A.subgroupOf U from ha)) ⟨u, hu⟩
      rwa [mem_subgroupOf] at this
    have := M.mul_mem (M.mul_mem (hDM hd) h1) (M.inv_mem (hDM hd))
    rwa [show d * (u * a * u⁻¹) * d⁻¹ = d * u * a * (d * u)⁻¹ by group] at this
  have hSyl : ¬ 2 ∣ S.relIndex U := fun hd =>
    h.not_dvd_index (hd.trans (relIndex_dvd_index_of_le hSU))
  have hcard : Nat.card U < Nat.card H := by
    have := card_lt_of_lt (lt_top_iff_ne_top.mpr hU)
    rwa [card_top] at this
  obtain ⟨L', hL'⟩ := ih U hPU hcard (h.subgroupOf hSyl hcoatom hcore)
  rcases hL' with hL' | hL'
  · exact ⟨_, Or.inl (hL'.map_subtype hAU)⟩
  · exact ⟨_, Or.inr (hL'.map_subtype hAU)⟩

theorem exists_isL24_or_isL24Sz_of_comap_ne_top {Lb : Subgroup (H ⧸ M.normalCore)}
    (hPL : P (Lb.comap (QuotientGroup.mk' M.normalCore))) (ih : IH24Of P (Nat.card H))
    (h : Hyp24 S M A) (hSD : S ⊓ M.normalCore = ⊥) (hDodd : ¬ 2 ∣ Nat.card M.normalCore)
    (hLb : IsL24Core (S.map (QuotientGroup.mk' M.normalCore))
      (M.map (QuotientGroup.mk' M.normalCore)) (A.map (QuotientGroup.mk' M.normalCore)) Lb)
    (hL₁ : Lb.comap (QuotientGroup.mk' M.normalCore) ≠ ⊤) :
    ∃ L, IsL24 S M A L ∨ IsL24Sz S M A L := by
  set D := M.normalCore with hDdef
  set π := QuotientGroup.mk' D with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective D
  have hker : π.ker = D := QuotientGroup.ker_mk' D
  have hDM : D ≤ M := normalCore_le M
  set L₁ := Lb.comap π with hL₁def
  have hDL₁ : D ≤ L₁ := by rw [← hker]; exact MonoidHom.ker_le_comap π Lb
  have hAL₁ : A ≤ L₁ := map_le_iff_le_comap.mp hLb.le
  have hmapL₁ : L₁.map π = Lb := map_comap_eq_self_of_surjective hπs Lb
  have hcM : (M.map π).comap π = M := by rw [comap_map_eq, hker, sup_of_le_left hDM]
  have hnotM : ∀ x, x ∉ M → π x ∉ M.map π := fun x hx hxM => hx (by rw [← hcM]; exact hxM)
  have hSyl : ¬ 2 ∣ S.relIndex L₁ := by
    have h1 : S.relIndex ((S ⊔ D) ⊓ L₁) * (S ⊔ D).relIndex L₁ = S.relIndex L₁ := by
      rw [relIndex_inf_mul_relIndex S (S ⊔ D) L₁, inf_of_le_left (le_sup_left : S ≤ S ⊔ D)]
    have h2 : (S ⊔ D).relIndex L₁ = (S.map π).relIndex Lb := by
      rw [show S ⊔ D = (S.map π).comap π by rw [comap_map_eq, hker], relIndex_comap, hmapL₁]
    have h3 : S.relIndex ((S ⊔ D) ⊓ L₁) = Nat.card D := by
      have hX : (S ⊔ D) ⊓ L₁ = (S ⊓ L₁) ⊔ D := by
        rw [inf_comm, ← Subgroup.inf_sup_assoc_of_le
          (by rw [normalizer_eq_top_iff.mpr inferInstance]; exact le_top) hDL₁, inf_comm L₁ S]
      have hSX : S ⊓ ((S ⊔ D) ⊓ L₁) = S ⊓ L₁ := by
        rw [← inf_assoc, inf_of_le_left (le_sup_left : S ≤ S ⊔ D)]
      have hSLD : S ⊓ L₁ ⊓ D = ⊥ := by
        rw [inf_right_comm, hSD, bot_inf_eq]
      rw [← inf_relIndex_right S, hSX, hX, relIndex_sup_of_normal, ← inf_relIndex_right, hSLD,
        relIndex_bot_left]
    rw [← h1, h2, h3]
    intro hd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with hd | hd
    · exact hDodd hd
    · exact hLb.not_dvd_relIndex hd
  have hcoatom : IsCoatom (M.subgroupOf L₁) := by
    refine ⟨fun htop => hLb.not_le ?_, fun K hK => ?_⟩
    · rw [← hmapL₁]
      refine map_mono fun x hx => ?_
      have : (⟨x, hx⟩ : L₁) ∈ M.subgroupOf L₁ := by
        rw [htop]
        exact mem_top _
      exact this
    · obtain ⟨k, hkK, hkM⟩ := SetLike.exists_of_lt hK
      have hkM' : (k : H) ∉ M := by rwa [mem_subgroupOf] at hkM
      set K₁ := K.map L₁.subtype with hK₁
      have hMK : M ⊓ L₁ ≤ K₁ := by
        intro x hx
        exact ⟨⟨x, hx.2⟩, hK.le (by rw [mem_subgroupOf]; exact hx.1), rfl⟩
      have hK₁L : K₁ ≤ L₁ := map_subtype_le K
      have hK₁map : K₁.map π = Lb :=
        hLb.eq_of_le ((map_mono hK₁L).trans hmapL₁.le)
          (map_mono ((le_inf (h.le_S.trans h.le_M) hAL₁).trans hMK))
          fun hle => hnotM k hkM' (hle ⟨k, ⟨k, hkK, rfl⟩, rfl⟩)
      have hK₁eq : K₁ = L₁ := by
        rw [hL₁def, ← hK₁map, comap_map_eq, hker, sup_of_le_left ((le_inf hDM hDL₁).trans hMK)]
      rw [eq_top_iff]
      intro x _
      have : (x : H) ∈ K₁ := by rw [hK₁eq]; exact x.2
      obtain ⟨y, hy, hyx⟩ := this
      rwa [show y = x from Subtype.ext hyx] at hy
  have hcore : ¬ A.subgroupOf L₁ ≤ (M.subgroupOf L₁).normalCore := by
    intro hle
    obtain ⟨xb, hxbL, hxbM⟩ : ∃ xb ∈ Lb, xb ∉ M.map π := Set.not_subset.mp hLb.not_le
    obtain ⟨x, rfl⟩ := hπs xb
    have hxL₁ : x ∈ L₁ := hxbL
    have hconj : A.map (MulAut.conj x).toMonoidHom ≤ M := by
      intro z hz
      obtain ⟨a, ha, rfl⟩ := mem_map_conj.mp hz
      have := mem_normalCore_iff.mp
        (hle (show (⟨a, hAL₁ ha⟩ : L₁) ∈ A.subgroupOf L₁ from ha)) ⟨x, hxL₁⟩
      rwa [mem_subgroupOf] at this
    apply hLb.not_le
    rw [← hLb.sup_conj (π x) hxbL hxbM, ← map_map_conj, ← Subgroup.map_sup]
    exact map_mono (sup_le (h.le_S.trans h.le_M) hconj)
  have hcard : Nat.card L₁ < Nat.card H := by
    have := card_lt_of_lt (lt_top_iff_ne_top.mpr hL₁)
    rwa [card_top] at this
  obtain ⟨L', hL'⟩ := ih L₁ hPL hcard (h.subgroupOf hSyl hcoatom hcore)
  rcases hL' with hL' | hL'
  · exact ⟨_, Or.inl (hL'.map_subtype hAL₁)⟩
  · exact ⟨_, Or.inr (hL'.map_subtype hAL₁)⟩

theorem isL24Sz_top_of_comap_eq_top (h : Hyp24 S M A) (hO : oTwo H = ⊥)
    (hstar : ∀ U : Subgroup H, S ≤ U → U ⊔ M.normalCore = ⊤ → U = ⊤)
    {Lb : Subgroup (H ⧸ M.normalCore)}
    (hLb : IsL24Sz (S.map (QuotientGroup.mk' M.normalCore))
      (M.map (QuotientGroup.mk' M.normalCore)) (A.map (QuotientGroup.mk' M.normalCore)) Lb)
    (hL₁ : Lb.comap (QuotientGroup.mk' M.normalCore) = ⊤) : IsL24Sz S M A ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := M.normalCore with hDdef
  set π := QuotientGroup.mk' D with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective D
  have hker : π.ker = D := QuotientGroup.ker_mk' D
  have hDM : D ≤ M := normalCore_le M
  have hcM : (M.map π).comap π = M := by rw [comap_map_eq, hker, sup_of_le_left hDM]
  have hnotM : ∀ x, x ∉ M → π x ∉ M.map π := fun x hx hxM => hx (by rw [← hcM]; exact hxM)
  have hLbtop : Lb = ⊤ := by
    rw [← map_comap_eq_self_of_surjective hπs Lb, hL₁, map_top_of_surjective π hπs]
  have hDodd := odd_card_normalCore h hO hstar
  have hOQ := oTwo_quotient_normalCore_eq_bot h hO hstar
  have hsup : ∀ x : H, x ∉ M → A ⊔ A.map (MulAut.conj x).toMonoidHom = ⊤ := by
    intro x hx
    set U := A ⊔ A.map (MulAut.conj x).toMonoidHom with hU
    have hUD : U ⊔ D = ⊤ := by
      have := hLb.sup_conj (π x) (by rw [hLbtop]; exact mem_top _) (hnotM x hx)
      rw [hLbtop, ← map_map_conj, ← Subgroup.map_sup] at this
      rw [← hker, ← comap_map_eq, this, comap_top]
    have hUi : ¬ 2 ∣ U.index := by
      rw [← relIndex_top_right, ← hUD, relIndex_sup_of_normal]
      exact fun hd => hDodd (hd.trans (relIndex_dvd_card U D))
    obtain ⟨T⟩ : Nonempty (Sylow 2 U) := inferInstance
    have hT2 : IsPGroup 2 ((T : Subgroup U).map U.subtype) := T.isPGroup'.map _
    have hTi : ¬ 2 ∣ ((T : Subgroup U).map U.subtype).index := by
      rw [index_map_subtype]
      intro hd
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with hd | hd
      · exact T.not_dvd_index hd
      · exact hUi hd
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H (h.isPGroup.toSylow h.not_dvd_index)
      (hT2.toSylow hTi)
    have hgS : ∀ s ∈ S, g * s * g⁻¹ ∈ U := by
      intro s hs
      have h1 : g * s * g⁻¹ ∈ ((g • h.isPGroup.toSylow h.not_dvd_index : Sylow 2 H) :
          Subgroup H) := by
        rw [Sylow.coe_subgroup_smul]
        exact Subgroup.smul_mem_pointwise_smul _ _ _ (by simpa using hs)
      rw [hg] at h1
      obtain ⟨t, -, ht⟩ := h1
      rw [← ht]
      exact t.2
    set U' := U.comap (MulAut.conj g).toMonoidHom with hU'
    have hSU' : S ≤ U' := fun s hs => hgS s hs
    have hU'D : U' ⊔ D = ⊤ := by
      rw [eq_top_iff]
      intro y _
      have hy : g * y * g⁻¹ ∈ ((U ⊔ D : Subgroup H) : Set H) := by
        rw [hUD]
        exact mem_top _
      rw [mul_normal] at hy
      obtain ⟨u, hu, d, hd, hud⟩ := hy
      have hud : u * d = g * y * g⁻¹ := hud
      have hy' : y = (g⁻¹ * u * g) * (g⁻¹ * d * g) := by
        rw [show g⁻¹ * u * g * (g⁻¹ * d * g) = g⁻¹ * (u * d) * g by group, hud]
        group
      rw [hy']
      refine mul_mem_sup ?_ ?_
      · change (MulAut.conj g) (g⁻¹ * u * g) ∈ U
        rwa [MulAut.conj_apply, show g * (g⁻¹ * u * g) * g⁻¹ = u by group]
      · have := (inferInstance : D.Normal).conj_mem d hd g⁻¹
        rwa [inv_inv] at this
    have hU'top := hstar U' hSU' hU'D
    rw [eq_top_iff]
    intro z _
    have hz : g⁻¹ * z * g ∈ U' := by rw [hU'top]; exact mem_top _
    change (MulAut.conj g) (g⁻¹ * z * g) ∈ U at hz
    rwa [MulAut.conj_apply, show g * (g⁻¹ * z * g) * g⁻¹ = z by group] at hz
  refine ⟨⟨le_top, fun htop => h.isCoatom.1 (eq_top_iff.mpr htop), ?_,
    fun x _ hx => hsup x hx⟩, ?_⟩
  · rw [relIndex_top_right]
    exact h.not_dvd_index
  · have h1 : SzOverOTwo (H ⧸ D) :=
      hLb.suzuki.of_mulEquiv ((MulEquiv.subgroupCongr hLbtop).trans Subgroup.topEquiv).symm
    have h2 : SzOverOTwo H := h1.of_surjective_odd π hπs (by rw [hker]; exact hDodd) hO hOQ
    exact h2.of_mulEquiv Subgroup.topEquiv

theorem exists_isL24_of_minimalNormal_solvable (h : Hyp24 S M A) (hO : oTwo H = ⊥)
    (hD : M.normalCore = ⊥) {N : Subgroup H} [hNn : N.Normal] (hNbot : N ≠ ⊥)
    (hmin : ∀ K : Subgroup H, K.Normal → K ≤ N → K = ⊥ ∨ K = N) (hNs : Group.IsSolvable N) :
    ∃ L, IsL24 S M A L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CFSG.IsMinimalNormal N := ⟨fun K _ hK => hmin K inferInstance hK⟩
  obtain ⟨p, hp, hNel'⟩ := CFSG.minimalNormal_solvable_exists_isElementaryAbelian N
  have hNel : CFSG.Open.IsElemAbelian p N :=
    ⟨hNel'.toIsMulCommutative, fun x hx => CFSG.elemPow_eq_one_of_isElementaryAbelian x hx⟩
  have : Fact p.Prime := ⟨hp⟩
  have hNp : IsPGroup p N := fun x => ⟨1, Subtype.ext (by simpa using hNel.2 _ x.2)⟩
  obtain ⟨k, hNcard⟩ := hNp.exists_card_eq
  have hp2 : p ≠ 2 := by
    rintro rfl
    apply hNbot
    rw [eq_bot_iff, ← hO]
    exact le_oTwo (IsPGroup.of_card hNcard)
  have hNM : ¬ N ≤ M := fun hle => hNbot (by
    rw [eq_bot_iff, ← hD]
    exact normal_le_normalCore.mpr hle)
  have hMN : M ⊔ N = ⊤ :=
    h.isCoatom.2 _ (lt_of_le_of_ne le_sup_left fun heq => hNM (heq ▸ le_sup_right))
  have hcop : Nat.Coprime 2 (Nat.card N) := by
    rw [hNcard]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have hNc : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := fun x hx y hy => isElemAbelian_comm hNel hx hy
  obtain ⟨B, hBA, hcardB, c, ⟨hcN, hcB⟩, a, haA, hy⟩ :=
    exists_hyperplane_conj_not_mem h hNc hcop hMN
  set y := c⁻¹ * (a * c * a⁻¹) with hydef
  have ha2 : a * a = 1 := by rw [← pow_two]; exact h.elemAb.2 a haA
  have hBc : ∀ b ∈ B, b * c = c * b := fun b hb => mem_centralizer_iff.mp hcB b hb
  have haB : a ∉ B := fun haB => hy (by
    rw [hydef, hBc a haB, mul_inv_cancel_right, inv_mul_cancel]
    exact M.one_mem)
  have hidx : B.relIndex A = 2 := by
    have := relIndex_mul_card B A
    rw [inf_of_le_left hBA, hcardB] at this
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos this
  have hyB : y ∈ centralizer (B : Set H) := by
    have hcaB : a * c * a⁻¹ ∈ centralizer (B : Set H) := by
      rw [mem_centralizer_iff]
      intro b hb
      have hba : Commute b a := (isElemAbelian_comm h.elemAb haA (hBA hb)).symm
      have hbc : Commute b c := hBc b hb
      exact ((hba.mul_right hbc).mul_right hba.inv_right).eq
    exact mul_mem (inv_mem hcB) hcaB
  have hay : a * y * a⁻¹ = y⁻¹ := by
    have e1 : a * y * a⁻¹ = a * c⁻¹ * a⁻¹ * (a * a * c * (a * a)⁻¹) := by rw [hydef]; group
    rw [e1, ha2, one_mul, inv_one, mul_one, hydef]
    group
  have hyN : y ∈ N := N.mul_mem (N.inv_mem hcN) (hNn.conj_mem c hcN a)
  have hy1 : y ≠ 1 := fun h1 => hy (by rw [h1]; exact M.one_mem)
  have hyp : orderOf y = p := orderOf_eq_prime (hNel.2 y hyN) hy1
  exact ⟨_, isL24_zpowers_sup h hBA hidx haA haB hyB hay hp hp2 hyp hy⟩

end Steps

theorem exists_isL24_or_isL24Sz_aux (P : ∀ (G : Type u) [Group G], Prop)
    (hsub : ∀ (G : Type u) [Group G] (K : Subgroup G), P G → P K)
    (hquot : ∀ (G : Type u) [Group G] (N : Subgroup G) [N.Normal], P G → P (G ⧸ N))
    (step : Step24 P) (n : ℕ) :
    ∀ (H : Type u) [Group H] [Finite H], P H → Nat.card H = n →
      ∀ {S M A : Subgroup H}, Hyp24 S M A → ∃ L, IsL24 S M A L ∨ IsL24Sz S M A L := by
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro H _ _ hP hn S M A h
  have ih : IH24Of P (Nat.card H) := fun G _ _ hPG hG S' M' A' h' =>
    ihn _ (hn ▸ hG) G hPG rfl h'
  by_cases hO : oTwo H = ⊥
  swap
  · exact exists_isL24_or_isL24Sz_of_oTwo_ne_bot (hquot H _ hP) ih h hO
  by_cases hU : ∃ U : Subgroup H, S ≤ U ∧ U ⊔ M.normalCore = ⊤ ∧ U ≠ ⊤
  · obtain ⟨U, hSU, hUD, hU⟩ := hU
    exact exists_isL24_or_isL24Sz_of_sup_normalCore (hsub H U hP) ih h hSU hUD hU
  have hstar : ∀ U : Subgroup H, S ≤ U → U ⊔ M.normalCore = ⊤ → U = ⊤ := by
    intro U hSU hUD
    by_contra hU'
    exact hU ⟨U, hSU, hUD, hU'⟩
  by_cases hD : M.normalCore = ⊥
  ·
    have hnt : (⊤ : Subgroup H) ≠ ⊥ := fun htop => h.isCoatom.1 (by
      rw [eq_top_iff, htop]
      exact bot_le)
    obtain ⟨N, hNn, -, hN1, hmin⟩ := CFSG.exists_minimal_normal_le (⊤ : Subgroup H)
      inferInstance hnt
    have hmin' : ∀ K : Subgroup H, K.Normal → K ≤ N → K = ⊥ ∨ K = N := fun K hK hKN =>
      (em (K = ⊥)).imp id fun hK1 => hmin K hK hKN hK1
    by_cases hNs : Group.IsSolvable N
    · exact (exists_isL24_of_minimalNormal_solvable h hO hD hN1 hmin' hNs).imp
        fun L hL => Or.inl hL
    · exact step H hP h hO hD N hNn hN1 hmin' hNs
  have hcard : Nat.card (H ⧸ M.normalCore) < Nat.card H := by
    rw [card_eq_card_quotient_mul_card_subgroup M.normalCore]
    have h1 : 1 < Nat.card M.normalCore := (one_lt_card_iff_ne_bot _).mpr hD
    have h2 := Nat.card_pos (α := H ⧸ M.normalCore)
    nlinarith
  obtain ⟨Lb, hLb⟩ := ih _ (hquot H _ hP) hcard (h.map_quotient M.normalCore (normalCore_le M))
  by_cases hL₁ : Lb.comap (QuotientGroup.mk' M.normalCore) = ⊤
  · rcases hLb with hLb | hLb
    · exact ⟨⊤, Or.inl (isL24_top_of_comap_eq_top h hO hstar hLb hL₁)⟩
    · exact ⟨⊤, Or.inr (isL24Sz_top_of_comap_eq_top h hO hstar hLb hL₁)⟩
  · exact exists_isL24_or_isL24Sz_of_comap_ne_top (hsub H _ hP) ih h
      (inf_normalCore_eq_bot h hO hstar) (odd_card_normalCore h hO hstar)
      (hLb.elim IsL24.toCore (·.toIsL24Core)) hL₁

theorem exists_isL24_or_isL24Sz_of_step (P : ∀ (G : Type u) [Group G], Prop)
    (hsub : ∀ (G : Type u) [Group G] (K : Subgroup G), P G → P K)
    (hquot : ∀ (G : Type u) [Group G] (N : Subgroup G) [N.Normal], P G → P (G ⧸ N))
    (step : Step24 P) {H : Type u} [Group H] [Finite H] (hP : P H) {S M A : Subgroup H}
    (h : Hyp24 S M A) : ∃ L, IsL24 S M A L ∨ IsL24Sz S M A L :=
  exists_isL24_or_isL24Sz_aux P hsub hquot step _ H hP rfl h

theorem exists_isL24_or_isL24Sz_of_step_subgroup (P : ∀ (G : Type u) [Group G], Prop)
    (hsub : ∀ (G : Type u) [Group G] (K : Subgroup G), P G → P K)
    (hquot : ∀ (G : Type u) [Group G] (N : Subgroup G) [N.Normal], P G → P (G ⧸ N))
    (step : Step24 P) {G : Type u} [Group G] [Finite G] {H : Subgroup G} (hP : P H)
    {S M A : Subgroup G} (hS : IsPGroup 2 S) (hSH : S ≤ H) (hSi : ¬ 2 ∣ S.relIndex H)
    (hMH : M ≤ H) (hM : IsCoatom (M.subgroupOf H)) (hSM : S ≤ M) (hAS : A ≤ S)
    (hA : CFSG.Open.IsElemAbelian 2 A) (hAD : ∃ h ∈ H, ∃ a ∈ A, h * a * h⁻¹ ∉ M) :
    ∃ L ≤ H, IsL24 S M A L ∨ IsL24Sz S M A L := by
  have hAH : A ≤ H := hAS.trans hSH
  have hcore : ¬ A.subgroupOf H ≤ (M.subgroupOf H).normalCore := by
    intro hle
    obtain ⟨g, hg, a, ha, hgaM⟩ := hAD
    have := mem_normalCore_iff.mp (hle (show (⟨a, hAH ha⟩ : H) ∈ A.subgroupOf H from ha))
      ⟨g, hg⟩
    rw [mem_subgroupOf] at this
    exact hgaM this
  obtain ⟨L', hL'⟩ := exists_isL24_or_isL24Sz_of_step P hsub hquot step (H := H) hP
    (S := S.subgroupOf H) (M := M.subgroupOf H) (A := A.subgroupOf H)
    ⟨hS.comap_subtype, hSi, hM, fun _ hx => hSM hx, fun _ hx => hAS hx,
      isElemAbelian_subgroupOf hA, hcore⟩
  rcases hL' with hL' | hL'
  · exact ⟨_, map_subtype_le L', Or.inl (hL'.map_subtype hAH)⟩
  · exact ⟨_, map_subtype_le L', Or.inr (hL'.map_subtype hAH)⟩

end CFSG.RankThree.S4Free.Stell
