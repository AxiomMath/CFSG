module

public import CFSG.RankThree.S4Free.Basic
public import CFSG.Open.LocalVocabulary
import CFSG.Quasithin.Background.RonanF95Dihedral
import CFSG.LocalAnalysis.SignalizerFunctor.MinimalNormal
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
import TauCeti.Algebra.Group.Subgroup.ModularLaw
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

universe u

namespace CFSG.RankThree.S4Free.Stell

open Subgroup
open scoped Pointwise

section OTwo

variable {X : Type*} [Group X]

theorem isPiSubgroup_two_of_isPGroup [Finite X] {K : Subgroup X} (hK : IsPGroup 2 K) :
    CFSG.IsPiSubgroup ({⟨2, Nat.prime_two⟩} : Set Nat.Primes) K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hK.exists_card_eq
  intro q hq
  rw [hn] at hq
  exact Set.mem_singleton_iff.mpr
    (Subtype.ext ((Nat.prime_dvd_prime_iff_eq q.2 Nat.prime_two).mp (q.2.dvd_of_dvd_pow hq)))

theorem le_oTwo [Finite X] {K : Subgroup X} [K.Normal] (hK : IsPGroup 2 K) : K ≤ oTwo X :=
  CFSG.LocalCores.le_piCore_of_normal inferInstance (isPiSubgroup_two_of_isPGroup hK)

theorem oTwo_isPGroup (X : Type*) [Group X] [Finite X] : IsPGroup 2 (oTwo X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hπ := CFSG.LocalCores.piCore_isPiSubgroup (G := X)
    ({⟨2, Nat.prime_two⟩} : Set Nat.Primes)
  rw [IsPGroup.iff_card]
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {d} hd hdN => ?_⟩
  have := hπ ⟨d, hd⟩ hdN
  simpa using congrArg Subtype.val (Set.mem_singleton_iff.mp this)

theorem eq_one_of_mem_oTwo [Finite X] {x : X} (hx : x ∈ oTwo X) (hodd : ¬ 2 ∣ orderOf x) :
    x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp (oTwo_isPGroup X) ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at hk
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  · exact absurd (hk ▸ dvd_pow_self 2 (Nat.succ_ne_zero k)) hodd

variable {Y : Type*} [Group Y]

theorem comap_oTwo_eq [Finite X] (f : X →* Y) (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) : (oTwo Y).comap f = oTwo X := by
  have : Finite Y := Finite.of_surjective f hf
  apply le_antisymm
  · exact le_oTwo ((oTwo_isPGroup Y).comap_of_ker_isPGroup f hker)
  · intro x hx
    have : ((oTwo X).map f).Normal := (inferInstance : (oTwo X).Normal).map f hf
    exact le_oTwo ((oTwo_isPGroup X).map f) (mem_map_of_mem f hx)

theorem nonempty_quotient_oTwo_mulEquiv [Finite X] (f : X →* Y) (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) : Nonempty (X ⧸ oTwo X ≃* Y ⧸ oTwo Y) := by
  let φ : X →* Y ⧸ oTwo Y := (QuotientGroup.mk' (oTwo Y)).comp f
  have hφ : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hf
  have hker' : oTwo X = φ.ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', comap_oTwo_eq f hf hker]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker').trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩

theorem nonempty_quotient_oTwo_mulEquiv_of_mulEquiv [Finite X] (e : X ≃* Y) :
    Nonempty (X ⧸ oTwo X ≃* Y ⧸ oTwo Y) := by
  refine nonempty_quotient_oTwo_mulEquiv e.toMonoidHom e.surjective ?_
  have : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e.injective
  rw [this]
  exact IsPGroup.of_bot

end OTwo

section Basic

variable {G : Type*} [Group G]

theorem relIndex_sup_of_normal [Finite G] (H K : Subgroup G) [K.Normal] :
    H.relIndex (H ⊔ K) = H.relIndex K := by
  have h1 := relIndex_mul_relIndex (H ⊓ K) H (H ⊔ K) inf_le_left le_sup_left
  have h2 := relIndex_mul_relIndex (H ⊓ K) K (H ⊔ K) inf_le_right le_sup_right
  have h3 : K.relIndex (H ⊔ K) = (H ⊓ K).relIndex H := by
    rw [relIndex_sup_right, inf_relIndex_left]
  rw [h3, inf_relIndex_right, ← h1] at h2
  have hpos : (H ⊓ K).relIndex H ≠ 0 := by
    intro h0
    have := relIndex_mul_card (H ⊓ K) H
    rw [h0, zero_mul] at this
    exact Nat.card_pos.ne' this.symm
  exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hpos) (by rw [mul_comm] at h2; exact h2)).symm

theorem map_map_conj {G' : Type*} [Group G'] (f : G →* G') (A : Subgroup G) (x : G) :
    (A.map (MulAut.conj x).toMonoidHom).map f = (A.map f).map (MulAut.conj (f x)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext a
  simp [MulAut.conj_apply, map_mul, map_inv]

theorem mem_map_conj {A : Subgroup G} {x z : G} :
    z ∈ A.map (MulAut.conj x).toMonoidHom ↔ ∃ a ∈ A, x * a * x⁻¹ = z := by
  simp [Subgroup.mem_map, MulAut.conj_apply]

theorem map_conj_le {A K : Subgroup G} {x : G} (hAK : A ≤ K) (hx : x ∈ K) :
    A.map (MulAut.conj x).toMonoidHom ≤ K := by
  intro z hz
  obtain ⟨a, ha, rfl⟩ := mem_map_conj.mp hz
  exact K.mul_mem (K.mul_mem hx (hAK ha)) (K.inv_mem hx)

end Basic

section Dihedral

variable {G : Type*} [Group G]

theorem card_map_of_inf_ker_eq_bot {G' : Type*} [Group G'] (f : G →* G') {K : Subgroup G}
    (hK : K ⊓ f.ker = ⊥) : Nat.card (K.map f) = Nat.card K := by
  have hinj : Function.Injective (f.comp K.subtype) := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have : (k : G) ∈ K ⊓ f.ker := ⟨k.2, hk⟩
    rw [hK, mem_bot] at this
    exact Subtype.ext this
  have hrange : K.map f = (f.comp K.subtype).range := by
    rw [← MonoidHom.map_range, K.range_subtype]
  rw [hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem zpowers_le_normalizer_of_inv {a c : G} (ha : a * a = 1) (hac : a * c * a⁻¹ = c⁻¹) :
    zpowers a ≤ normalizer ((zpowers c : Subgroup G) : Set G) := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have key : ∀ k : ℤ, a * c ^ k * a⁻¹ = c ^ (-k) := fun k => by
    rw [← conj_zpow, hac, inv_zpow']
  rw [zpowers_le, mem_normalizer_iff]
  intro z
  rw [mem_zpowers_iff, mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨-k, (key k).symm⟩
  · rintro ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    have h1 : z = a⁻¹ * c ^ k * a := by rw [hk]; group
    rw [h1, show a⁻¹ * c ^ k * a = a * c ^ k * a⁻¹ by rw [hai], key]

theorem eq_of_prime_dvd_orderOf [Finite G] {a g : G} {D : Subgroup G} [D.Normal]
    (ha : a * a = 1) (hag : a * g * a⁻¹ = g⁻¹) (hgen : zpowers a ⊔ zpowers g = ⊤)
    (hodd : ¬ 2 ∣ orderOf g) {r s : ℕ} (hr : r.Prime) (hQ : Nat.card (G ⧸ D) = 2 * r ^ s)
    (hstar : ∀ U : Subgroup G, a ∈ U → U ⊔ D = ⊤ → U = ⊤) {q : ℕ} (hq : q.Prime)
    (hqm : q ∣ orderOf g) : q = r := by
  by_contra hqr
  have hq2 : q ≠ 2 := by
    rintro rfl
    exact hodd hqm
  obtain ⟨e, m', hqm', hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' q
    hq.ne_one
  have he : e ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hm
    exact hqm' (hm ▸ hqm)
  have hgD : g ^ m' ∈ D := by
    rw [← QuotientGroup.eq_one_iff]
    have h1 : ((g ^ m' : G) : G ⧸ D) ^ q ^ e = 1 := by
      rw [← QuotientGroup.mk_pow, ← pow_mul, mul_comm, ← hm, pow_orderOf_eq_one,
        QuotientGroup.mk_one]
    have h2 : ((g ^ m' : G) : G ⧸ D) ^ Nat.card (G ⧸ D) = 1 := pow_card_eq_one'
    have hcop : Nat.Coprime (q ^ e) (Nat.card (G ⧸ D)) := by
      rw [hQ]
      refine Nat.Coprime.pow_left _ (Nat.Coprime.mul_right ?_ (Nat.Coprime.pow_right _ ?_))
      · exact (Nat.coprime_primes hq Nat.prime_two).mpr hq2
      · exact (Nat.coprime_primes hq hr).mpr hqr
    have := pow_gcd_eq_one.mpr ⟨h1, h2⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  set c := g ^ q ^ e with hc
  have hac : a * c * a⁻¹ = c⁻¹ := by rw [hc, ← conj_pow, hag, inv_pow]
  set U := zpowers c ⊔ zpowers a with hU
  have hUtop : U = ⊤ := by
    refine hstar U (mem_sup_right (mem_zpowers a)) ?_
    rw [eq_top_iff, ← hgen]
    refine sup_le ((zpowers_le.mpr (mem_sup_right (mem_zpowers a))).trans le_sup_left) ?_
    rw [zpowers_le]
    have hcop : Nat.Coprime (q ^ e) m' := Nat.Coprime.pow_left _
      ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqm')
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    have hg : g = c ^ u * (g ^ m') ^ v := by
      rw [hc, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, mul_comm,
        mul_comm (m' : ℤ), huv, zpow_one]
    rw [hg]
    exact mul_mem_sup (mem_sup_left (zpow_mem (mem_zpowers c) u)) (zpow_mem hgD v)
  have hgU : g ∈ (U : Set G) := by rw [hUtop]; exact mem_top g
  rw [hU, coe_mul_of_right_le_normalizer_left _ _ (zpowers_le_normalizer_of_inv ha hac)] at hgU
  obtain ⟨_, ⟨i, rfl⟩, t, ht, hgt⟩ := hgU
  have hgt : c ^ i * t = g := hgt
  have ht1 : t = 1 := by
    have htg : t ∈ zpowers g := by
      have : t = (c ^ i)⁻¹ * g := by rw [← hgt, inv_mul_cancel_left]
      rw [this, hc]
      exact mul_mem (inv_mem (zpow_mem (pow_mem (mem_zpowers g) _) i)) (mem_zpowers g)
    have h1 : orderOf t ∣ orderOf g := orderOf_dvd_of_mem_zpowers htg
    have h2 : orderOf t ∣ 2 := (orderOf_dvd_of_mem_zpowers ht).trans
      (orderOf_dvd_of_pow_eq_one (by rw [pow_two, ha]))
    have hcop : Nat.Coprime (orderOf g) 2 :=
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd))
    have h3 : orderOf t ∣ 1 := by
      have := Nat.dvd_gcd h1 h2
      rwa [hcop.gcd_eq_one] at this
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  rw [ht1, mul_one, hc, ← zpow_natCast, ← zpow_mul] at hgt
  have h1 : g ^ ((q ^ e : ℕ) * i - 1 : ℤ) = 1 := by
    rw [zpow_sub, hgt, zpow_one, mul_inv_cancel]
  rw [← orderOf_dvd_iff_zpow_eq_one] at h1
  have h2 : (q : ℤ) ∣ (q ^ e : ℕ) * i - 1 := (Int.natCast_dvd_natCast.mpr hqm).trans h1
  have h3 : (q : ℤ) ∣ (q ^ e : ℕ) * i := by
    refine Dvd.dvd.mul_right ?_ _
    exact Int.natCast_dvd_natCast.mpr (dvd_pow_self q he)
  have h4 : (q : ℤ) ∣ 1 := by
    have := dvd_sub h3 h2
    rwa [sub_sub_cancel] at this
  exact hq.ne_one (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h4)

theorem le_normalizer_zpowers {T : Subgroup G} {y : G}
    (h : ∀ t ∈ T, t * y * t⁻¹ ∈ zpowers y) : T ≤ normalizer ((zpowers y : Subgroup G) : Set G) := by
  intro t ht
  rw [mem_normalizer_iff]
  intro z
  constructor
  · rintro ⟨j, rfl⟩
    simp only
    rw [← conj_zpow]
    exact zpow_mem (h t ht) j
  · intro hz
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hz
    have h1 : z = t⁻¹ * y ^ j * t⁻¹⁻¹ := by rw [hj]; group
    rw [h1, ← conj_zpow]
    exact zpow_mem (h t⁻¹ (inv_mem ht)) j

theorem mem_or_inv_mul_mem {A B : Subgroup G} (hidx : B.relIndex A = 2) {a t : G} (ha : a ∈ A)
    (haB : a ∉ B) (ht : t ∈ A) : t ∈ B ∨ a⁻¹ * t ∈ B := by
  by_cases htB : t ∈ B
  · exact Or.inl htB
  · right
    have key := mul_mem_iff_of_index_two (H := B.subgroupOf A) hidx
      (a := (⟨a, ha⟩ : A)⁻¹) (b := ⟨t, ht⟩)
    have h1 : (⟨a, ha⟩ : A)⁻¹ ∉ B.subgroupOf A := by
      rw [inv_mem_iff, mem_subgroupOf]
      exact haB
    have h2 : (⟨t, ht⟩ : A) ∉ B.subgroupOf A := by
      rw [mem_subgroupOf]
      exact htB
    have := key.mpr ⟨fun h => absurd h h1, fun h => absurd h h2⟩
    rwa [mem_subgroupOf] at this

end Dihedral

structure Hyp24 {H : Type*} [Group H] (S M A : Subgroup H) : Prop where
  isPGroup : IsPGroup 2 S
  not_dvd_index : ¬ 2 ∣ S.index
  isCoatom : IsCoatom M
  le_M : S ≤ M
  le_S : A ≤ S
  elemAb : CFSG.Open.IsElemAbelian 2 A
  not_le_normalCore : ¬ A ≤ M.normalCore

structure IsL24 {H : Type*} [Group H] (S M A L : Subgroup H) : Prop where
  le : A ≤ L
  not_le : ¬ L ≤ M
  not_dvd_relIndex : ¬ 2 ∣ S.relIndex L
  sup_conj : ∀ x ∈ L, x ∉ M → A ⊔ A.map (MulAut.conj x).toMonoidHom = L
  dihedral : ∃ r s : ℕ, r.Prime ∧ r ≠ 2 ∧ 1 ≤ s ∧
    Nonempty (↥L ⧸ oTwo ↥L ≃* DihedralGroup (r ^ s))

section Statement

variable {H : Type*} [Group H] {S M A L K : Subgroup H}

theorem IsL24.eq_of_le (h : IsL24 S M A L) (hKL : K ≤ L) (hAK : A ≤ K) (hKM : ¬ K ≤ M) :
    K = L := by
  obtain ⟨x, hxK, hxM⟩ := Set.not_subset.mp hKM
  refine le_antisymm hKL ?_
  rw [← h.sup_conj x (hKL hxK) hxM]
  exact sup_le hAK (map_conj_le hAK hxK)

theorem IsL24.eq_of_inf_lt (h : IsL24 S M A L) (hAM : A ≤ M) (hKL : K ≤ L) (hlt : M ⊓ L < K) :
    K = L := by
  obtain ⟨x, hxK, hxML⟩ := SetLike.exists_of_lt hlt
  have hxM : x ∉ M := fun hxM => hxML ⟨hxM, hKL hxK⟩
  exact h.eq_of_le hKL ((le_inf hAM h.le).trans hlt.le) fun hKM => hxM (hKM hxK)

theorem IsL24.oTwo_le [Finite H] (h : IsL24 S M A L) (hS : IsPGroup 2 S) (hSM : S ≤ M) :
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

end Statement

section Transport

variable {H : Type*} [Group H] {S M A : Subgroup H}

theorem isElemAbelian_comm {p : ℕ} {E : Subgroup H} (hE : CFSG.Open.IsElemAbelian p E) {a b : H}
    (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a :=
  congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem isElemAbelian_of_forall {E : Subgroup H} (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (h2 : ∀ a ∈ E, a ^ 2 = 1) : CFSG.Open.IsElemAbelian 2 E :=
  ⟨⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, h2⟩

theorem isElemAbelian_map {H' : Type*} [Group H'] {E : Subgroup H}
    (hE : CFSG.Open.IsElemAbelian 2 E) (f : H →* H') : CFSG.Open.IsElemAbelian 2 (E.map f) := by
  refine isElemAbelian_of_forall ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, isElemAbelian_comm hE ha hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE.2 a ha, map_one]

theorem isElemAbelian_subgroupOf {E U : Subgroup H} (hE : CFSG.Open.IsElemAbelian 2 E) :
    CFSG.Open.IsElemAbelian 2 (E.subgroupOf U) :=
  isElemAbelian_of_forall (fun a ha b hb => Subtype.ext (isElemAbelian_comm hE ha hb))
    fun a ha => Subtype.ext (by simpa using hE.2 _ ha)

theorem isCoatom_map_of_surjective {H' : Type*} [Group H'] (f : H →* H')
    (hf : Function.Surjective f) {M : Subgroup H} (hM : IsCoatom M) (hker : f.ker ≤ M) :
    IsCoatom (M.map f) := by
  have hcm : (M.map f).comap f = M := by rw [comap_map_eq, sup_of_le_left hker]
  refine ⟨fun htop => hM.1 ?_, fun K hK => ?_⟩
  · rw [← hcm, htop, comap_top]
  · have hlt : M < K.comap f := by
      rw [← hcm]
      exact (comap_lt_comap_of_surjective hf).mpr hK
    rw [← map_comap_eq_self_of_surjective hf K, hM.2 _ hlt, map_top_of_surjective f hf]

theorem Hyp24.map_quotient (h : Hyp24 S M A) (N : Subgroup H) [N.Normal] (hNM : N ≤ M) :
    Hyp24 (S.map (QuotientGroup.mk' N)) (M.map (QuotientGroup.mk' N))
      (A.map (QuotientGroup.mk' N)) where
  isPGroup := h.isPGroup.map _
  not_dvd_index := fun hd =>
    h.not_dvd_index (hd.trans (index_map_dvd S (QuotientGroup.mk'_surjective N)))
  isCoatom := isCoatom_map_of_surjective _ (QuotientGroup.mk'_surjective N) h.isCoatom
    (by rwa [QuotientGroup.ker_mk'])
  le_M := map_mono h.le_M
  le_S := map_mono h.le_S
  elemAb := isElemAbelian_map h.elemAb _
  not_le_normalCore := by
    intro hle
    apply h.not_le_normalCore
    have hcm : (M.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) = M := by
      rw [comap_map_eq, QuotientGroup.ker_mk', sup_of_le_left hNM]
    have hC : ((M.map (QuotientGroup.mk' N)).normalCore.comap (QuotientGroup.mk' N)) ≤
        M.normalCore := by
      rw [normal_le_normalCore]
      calc _ ≤ (M.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) :=
            comap_mono (normalCore_le _)
        _ = M := hcm
    exact (map_le_iff_le_comap.mp hle).trans hC

theorem Hyp24.subgroupOf {U : Subgroup H} (h : Hyp24 S M A) (hSU : ¬ 2 ∣ S.relIndex U)
    (hcoatom : IsCoatom (M.subgroupOf U))
    (hcore : ¬ A.subgroupOf U ≤ (M.subgroupOf U).normalCore) :
    Hyp24 (S.subgroupOf U) (M.subgroupOf U) (A.subgroupOf U) where
  isPGroup := h.isPGroup.comap_subtype
  not_dvd_index := hSU
  isCoatom := hcoatom
  le_M := fun _ hx => h.le_M hx
  le_S := fun _ hx => h.le_S hx
  elemAb := isElemAbelian_subgroupOf h.elemAb
  not_le_normalCore := hcore

variable [Finite H]

theorem IsL24.map_subtype {U : Subgroup H} (hAU : A ≤ U) {L' : Subgroup U}
    (h : IsL24 (S.subgroupOf U) (M.subgroupOf U) (A.subgroupOf U) L') :
    IsL24 S M A (L'.map U.subtype) where
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
  dihedral := by
    obtain ⟨r, s, hr, hr2, hs, ⟨e⟩⟩ := h.dihedral
    obtain ⟨e'⟩ := nonempty_quotient_oTwo_mulEquiv_of_mulEquiv
      (L'.equivMapOfInjective U.subtype U.subtype_injective).symm
    exact ⟨r, s, hr, hr2, hs, ⟨e'.trans e⟩⟩

end Transport

@[expose] def IH24 (n : ℕ) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] [Group.IsSolvable G], Nat.card G < n →
    ∀ {S M A : Subgroup G}, Hyp24 S M A → ∃ L, IsL24 S M A L

section Steps

variable {H : Type u} [Group H] [Finite H] {S M A : Subgroup H}

theorem exists_minimal_subgroup (P : Subgroup H → Prop) (hP : ∃ K, P K) :
    ∃ K, P K ∧ ∀ K', P K' → K' ≤ K → K' = K := by
  obtain ⟨K, hK⟩ := exists_minimal_of_wellFoundedLT P hP
  exact ⟨K, hK.1, fun K' hK' hle => le_antisymm hle (hK.2 hK' hle)⟩

theorem relIndex_map_of_ker_le {H' : Type*} [Group H'] (f : H →* H') {S : Subgroup H}
    (hker : f.ker ≤ S) (L : Subgroup H) : (S.map f).relIndex (L.map f) = S.relIndex L := by
  rw [← relIndex_comap, comap_map_eq, sup_of_le_left hker]

theorem exists_isL24_of_oTwo_ne_bot [Group.IsSolvable H] (ih : IH24.{u} (Nat.card H))
    (h : Hyp24 S M A) (hO : oTwo H ≠ ⊥) : ∃ L, IsL24 S M A L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := oTwo H with hPdef
  set π := QuotientGroup.mk' P with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective P
  have hker : π.ker = P := QuotientGroup.ker_mk' P
  have hPS : P ≤ S := by
    have := (oTwo_isPGroup H).le_sylow_of_normal (h.isPGroup.toSylow h.not_dvd_index)
    simpa using this
  have hPM : P ≤ M := hPS.trans h.le_M
  have hcard : Nat.card (H ⧸ P) < Nat.card H := by
    rw [card_eq_card_quotient_mul_card_subgroup P]
    have h1 : 1 < Nat.card P := (one_lt_card_iff_ne_bot P).mpr hO
    have h2 := Nat.card_pos (α := H ⧸ P)
    nlinarith
  obtain ⟨Lb, hLb⟩ := ih (H ⧸ P) hcard (h.map_quotient P hPM)
  have hcM : (M.map π).comap π = M := by rw [comap_map_eq, hker, sup_of_le_left hPM]
  have hnotM : ∀ x, x ∉ M → π x ∉ M.map π := fun x hx hxM =>
    hx (by rw [← hcM]; exact hxM)
  set L₁ := Lb.comap π with hL₁
  obtain ⟨L, ⟨hAL, hLL₁, hLM⟩, hmin⟩ := exists_minimal_subgroup
    (fun K => A ≤ K ∧ K ≤ L₁ ∧ ¬ K ≤ M)
    ⟨L₁, map_le_iff_le_comap.mp hLb.le, le_rfl, fun hle => hLb.not_le (by
      rw [← map_comap_eq_self_of_surjective hπs Lb]
      exact map_mono hle)⟩
  have hLmap : L.map π = Lb :=
    hLb.eq_of_le (map_le_iff_le_comap.mpr hLL₁) (map_mono hAL) fun hle => hLM (by
      rw [← hcM]
      exact map_le_iff_le_comap.mp hle)
  refine ⟨L, hAL, hLM, ?_, ?_, ?_⟩
  · rw [← relIndex_map_of_ker_le π (by rw [hker]; exact hPS), hLmap]
    exact hLb.not_dvd_relIndex
  · intro x hxL hxM
    refine hmin _ ⟨le_sup_left, sup_le hAL (map_conj_le hAL hxL) |>.trans hLL₁, ?_⟩
      (sup_le hAL (map_conj_le hAL hxL))
    intro hle
    apply hLb.not_le
    rw [← hLb.sup_conj (π x) (hLL₁ hxL) (hnotM x hxM), ← map_map_conj, ← Subgroup.map_sup]
    exact map_mono hle
  · obtain ⟨r, s, hr, hr2, hs, ⟨e⟩⟩ := hLb.dihedral
    have hfker : (π.subgroupMap L).ker = P.comap L.subtype := by
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
    obtain ⟨e₁⟩ := nonempty_quotient_oTwo_mulEquiv (π.subgroupMap L)
      (π.subgroupMap_surjective L) hk2
    obtain ⟨e₂⟩ := nonempty_quotient_oTwo_mulEquiv_of_mulEquiv (MulEquiv.subgroupCongr hLmap)
    exact ⟨r, s, hr, hr2, hs, ⟨e₁.trans (e₂.trans e)⟩⟩

omit [Finite H] in
theorem mem_normalCore_iff {K : Subgroup H} {a : H} :
    a ∈ K.normalCore ↔ ∀ b : H, b * a * b⁻¹ ∈ K :=
  Iff.rfl

theorem exists_isL24_of_sup_normalCore [Group.IsSolvable H] (ih : IH24.{u} (Nat.card H))
    (h : Hyp24 S M A) {U : Subgroup H} (hSU : S ≤ U) (hUD : U ⊔ M.normalCore = ⊤)
    (hU : U ≠ ⊤) : ∃ L, IsL24 S M A L := by
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
  obtain ⟨L', hL'⟩ := ih U hcard (h.subgroupOf hSyl hcoatom hcore)
  exact ⟨_, hL'.map_subtype hAU⟩

theorem not_dvd_relIndex_of_normal (h : Hyp24 S M A) (N : Subgroup H) [N.Normal] :
    ¬ 2 ∣ S.relIndex N := by
  rw [← relIndex_sup_of_normal]
  exact fun hd => h.not_dvd_index (hd.trans (relIndex_dvd_index_of_le le_sup_left))

omit [Finite H] in
theorem le_normalizer_inf (N : Subgroup H) [N.Normal] :
    S ≤ normalizer ((S ⊓ N : Subgroup H) : Set H) := by
  intro s hs
  rw [mem_normalizer_iff]
  intro t
  constructor
  · rintro ⟨htS, htN⟩
    exact ⟨S.mul_mem (S.mul_mem hs htS) (S.inv_mem hs), (inferInstance : N.Normal).conj_mem t htN s⟩
  · rintro ⟨htS, htN⟩
    have h1 : t = s⁻¹ * (s * t * s⁻¹) * s := by group
    refine ⟨?_, ?_⟩
    · rw [h1]
      exact S.mul_mem (S.mul_mem (S.inv_mem hs) htS) hs
    · rw [h1]
      have := (inferInstance : N.Normal).conj_mem _ htN s⁻¹
      rwa [inv_inv] at this

theorem normalizer_inf_sup_eq_top (h : Hyp24 S M A) (N : Subgroup H) [N.Normal] :
    normalizer ((S ⊓ N : Subgroup H) : Set H) ⊔ N = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ((S ⊓ N).subgroupOf N) := h.isPGroup.to_inf_left.comap_subtype
  have hi : ¬ 2 ∣ ((S ⊓ N).subgroupOf N).index := by
    change ¬ 2 ∣ (S ⊓ N).relIndex N
    rw [inf_relIndex_right]
    exact not_dvd_relIndex_of_normal h N
  have := Sylow.normalizer_sup_eq_top (hp.toSylow hi)
  rwa [IsPGroup.toSylow_coe, subgroupOf_map_subtype, inf_of_le_left inf_le_right] at this

theorem normal_inf_of_star (h : Hyp24 S M A)
    (hstar : ∀ U : Subgroup H, S ≤ U → U ⊔ M.normalCore = ⊤ → U = ⊤) (N : Subgroup H) [N.Normal]
    (hN : N ≤ normalizer ((S ⊓ N : Subgroup H) : Set H) ⊔ M.normalCore) : (S ⊓ N).Normal := by
  rw [← normalizer_eq_top_iff]
  refine hstar _ (le_normalizer_inf N) ?_
  rw [eq_top_iff, ← normalizer_inf_sup_eq_top h N]
  exact sup_le le_sup_left hN

theorem inf_normalCore_eq_bot (h : Hyp24 S M A) (hO : oTwo H = ⊥)
    (hstar : ∀ U : Subgroup H, S ≤ U → U ⊔ M.normalCore = ⊤ → U = ⊤) :
    S ⊓ M.normalCore = ⊥ := by
  have hn := normal_inf_of_star h hstar M.normalCore le_sup_right
  rw [eq_bot_iff, ← hO]
  exact le_oTwo h.isPGroup.to_inf_left

theorem odd_card_normalCore (h : Hyp24 S M A) (hO : oTwo H = ⊥)
    (hstar : ∀ U : Subgroup H, S ≤ U → U ⊔ M.normalCore = ⊤ → U = ⊤) :
    ¬ 2 ∣ Nat.card M.normalCore := by
  have := not_dvd_relIndex_of_normal h M.normalCore
  rwa [← inf_relIndex_right, inf_normalCore_eq_bot h hO hstar, relIndex_bot_left] at this

theorem oTwo_quotient_normalCore_eq_bot (h : Hyp24 S M A) (hO : oTwo H = ⊥)
    (hstar : ∀ U : Subgroup H, S ≤ U → U ⊔ M.normalCore = ⊤ → U = ⊤) :
    oTwo (H ⧸ M.normalCore) = ⊥ := by
  set D := M.normalCore with hDdef
  set π := QuotientGroup.mk' D with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective D
  have hker : π.ker = D := QuotientGroup.ker_mk' D
  set P := (oTwo (H ⧸ D)).comap π with hPdef
  set T := S ⊓ P with hTdef
  have hPTD : P ≤ T ⊔ D := by
    rw [← relIndex_eq_one]
    have hodd : ¬ 2 ∣ (T ⊔ D).relIndex P := by
      intro hd
      apply not_dvd_relIndex_of_normal h P
      rw [← inf_relIndex_right]
      exact hd.trans (relIndex_dvd_of_le_left P le_sup_left)
    have hdvd : (T ⊔ D).relIndex P ∣ Nat.card (oTwo (H ⧸ D)) := by
      rw [← relIndex_map_of_ker_le π (by rw [hker]; exact le_sup_right),
        hPdef, map_comap_eq_self_of_surjective hπs]
      exact relIndex_dvd_card _ _
    obtain ⟨m, hm⟩ := (oTwo_isPGroup (H ⧸ D)).exists_card_eq
    rw [hm] at hdvd
    exact Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd).symm)
      hdvd
  have hn := normal_inf_of_star h hstar P
    (hPTD.trans (sup_le_sup_right (le_normalizer (H := T)) _))
  have hT : T = ⊥ := by
    rw [eq_bot_iff, ← hO]
    exact le_oTwo h.isPGroup.to_inf_left
  have hPD : P ≤ D := by
    have := hPTD
    rwa [hT, bot_sup_eq] at this
  rw [eq_bot_iff, ← map_comap_eq_self_of_surjective hπs (oTwo (H ⧸ D)), ← hPdef]
  calc P.map π ≤ D.map π := map_mono hPD
    _ = ⊥ := QuotientGroup.map_mk'_self D

theorem exists_isL24_of_comap_ne_top [Group.IsSolvable H] (ih : IH24.{u} (Nat.card H))
    (h : Hyp24 S M A) (hSD : S ⊓ M.normalCore = ⊥) (hDodd : ¬ 2 ∣ Nat.card M.normalCore)
    {Lb : Subgroup (H ⧸ M.normalCore)}
    (hLb : IsL24 (S.map (QuotientGroup.mk' M.normalCore)) (M.map (QuotientGroup.mk' M.normalCore))
      (A.map (QuotientGroup.mk' M.normalCore)) Lb)
    (hL₁ : Lb.comap (QuotientGroup.mk' M.normalCore) ≠ ⊤) : ∃ L, IsL24 S M A L := by
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
  obtain ⟨L', hL'⟩ := ih L₁ hcard (h.subgroupOf hSyl hcoatom hcore)
  exact ⟨_, hL'.map_subtype hAL₁⟩

theorem isL24_top_of_comap_eq_top (h : Hyp24 S M A) (hO : oTwo H = ⊥)
    (hstar : ∀ U : Subgroup H, S ≤ U → U ⊔ M.normalCore = ⊤ → U = ⊤)
    {Lb : Subgroup (H ⧸ M.normalCore)}
    (hLb : IsL24 (S.map (QuotientGroup.mk' M.normalCore)) (M.map (QuotientGroup.mk' M.normalCore))
      (A.map (QuotientGroup.mk' M.normalCore)) Lb)
    (hL₁ : Lb.comap (QuotientGroup.mk' M.normalCore) = ⊤) : IsL24 S M A ⊤ := by
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
  have hSD := inf_normalCore_eq_bot h hO hstar
  have hOQ := oTwo_quotient_normalCore_eq_bot h hO hstar
  obtain ⟨r, s, hr, hr2, hs, ⟨e⟩⟩ := hLb.dihedral
  have hQ : Nat.card (H ⧸ D) = 2 * r ^ s := by
    obtain ⟨e'⟩ := nonempty_quotient_oTwo_mulEquiv_of_mulEquiv
      ((MulEquiv.subgroupCongr hLbtop).trans Subgroup.topEquiv)
    have h1 := Nat.card_congr (e'.symm.trans e).toEquiv
    rw [DihedralGroup.nat_card] at h1
    have hc1 : Nat.card (oTwo (H ⧸ D)) = 1 := by rw [hOQ, card_bot]
    rw [← h1, card_eq_card_quotient_mul_card_subgroup (oTwo (H ⧸ D)), hc1, mul_one]
  have hSbar : Nat.card (S.map π) = 2 := by
    obtain ⟨k, hk⟩ := (h.isPGroup.map π).exists_card_eq
    have hidx := index_mul_card (S.map π)
    rw [hk, hQ] at hidx
    have hodd : ¬ 2 ∣ (S.map π).index := (h.map_quotient D hDM).not_dvd_index
    rw [hk]
    rcases k with _ | k
    · exfalso
      apply hodd
      rw [pow_zero, mul_one] at hidx
      exact ⟨r ^ s, hidx⟩
    · rcases k with _ | k
      · rfl
      · exfalso
        have h2 : 2 ∣ r ^ s := by
          have h4 : 2 * 2 ∣ 2 * r ^ s := ⟨(S.map π).index * 2 ^ k, by rw [← hidx]; ring⟩
          exact Nat.dvd_of_mul_dvd_mul_left two_pos h4
        exact hr2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).mp
          (Nat.prime_two.dvd_of_dvd_pow h2)).symm
  have hS2 : Nat.card S = 2 := by
    rw [← card_map_of_inf_ker_eq_bot π (by rw [hker]; exact hSD)]
    exact hSbar
  have hAbot : A ≠ ⊥ := fun hA => h.not_le_normalCore (by rw [hA]; exact bot_le)
  have hAS : A = S := by
    have hdvd : Nat.card A ∣ 2 := hS2 ▸ card_dvd_of_le h.le_S
    have h1 : Nat.card A ≠ 1 := fun h1 => hAbot (card_eq_one.mp h1)
    have hA2 : Nat.card A = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h' | h'
      · exact absurd h' h1
      · exact h'
    exact eq_of_le_of_card_ge h.le_S (by rw [hA2, hS2])
  have hsup : ∀ x : H, x ∉ M → A ⊔ A.map (MulAut.conj x).toMonoidHom = ⊤ := by
    intro x hx
    refine hstar _ (by rw [← hAS]; exact le_sup_left) ?_
    have := hLb.sup_conj (π x) (by rw [hLbtop]; exact mem_top _) (hnotM x hx)
    rw [hLbtop, ← map_map_conj, ← Subgroup.map_sup] at this
    rw [← hker, ← comap_map_eq, this, comap_top]
  refine ⟨le_top, fun htop => h.isCoatom.1 (eq_top_iff.mpr htop), ?_, fun x _ hx => hsup x hx, ?_⟩
  · rw [relIndex_top_right]
    exact h.not_dvd_index
  obtain ⟨x, -, hxM⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr h.isCoatom.1)
  obtain ⟨⟨a, haA⟩, ha1⟩ := ne_bot_iff_exists_ne_one.mp hAbot
  have ha1' : a ≠ 1 := fun h' => ha1 (Subtype.ext h')
  have ha : a * a = 1 := by rw [← pow_two]; exact h.elemAb.2 a haA
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hAz : A = zpowers a := by
    symm
    refine eq_of_le_of_card_ge (zpowers_le.mpr haA) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two, ha]) ha1', ← hS2, hAS]
  set b := x * a * x⁻¹ with hb
  have hb2 : b * b = 1 := by
    rw [hb, show x * a * x⁻¹ * (x * a * x⁻¹) = x * (a * a) * x⁻¹ by group, ha, mul_one,
      mul_inv_cancel]
  set g := a * b with hg
  have hag : a * g * a⁻¹ = g⁻¹ := by
    rw [hg, mul_inv_rev, hai, inv_eq_of_mul_eq_one_right hb2, ← mul_assoc, ha, one_mul]
  have hgen : zpowers a ⊔ zpowers g = ⊤ := by
    rw [eq_top_iff, ← hsup x hxM, hAz]
    refine sup_le le_sup_left ?_
    rw [MonoidHom.map_zpowers, zpowers_le]
    have hconj : (MulAut.conj x).toMonoidHom a = a⁻¹ * g := by
      rw [hg, inv_mul_cancel_left, hb]
      rfl
    rw [hconj]
    exact mul_mem (inv_mem (mem_sup_left (mem_zpowers a))) (mem_sup_right (mem_zpowers g))
  set m := orderOf g with hm
  have hm3 : 3 ≤ m := by
    by_contra hlt
    have hg2 : g ^ 2 = 1 := by
      have : m ∣ 2 := by
        rcases (show m = 1 ∨ m = 2 by have := orderOf_pos g; omega) with h' | h' <;>
          rw [h'] <;> norm_num
      exact orderOf_dvd_iff_pow_eq_one.mp this
    have hab : a * b = b * a := by
      have := inv_eq_of_mul_eq_one_right (show g * g = 1 by rw [← pow_two]; exact hg2)
      rw [hg, mul_inv_rev, hai, inv_eq_of_mul_eq_one_right hb2] at this
      exact this.symm
    have hcent : ∀ y : H, y * a = a * y := by
      intro y
      have hle : (⊤ : Subgroup H) ≤ centralizer ({a} : Set H) := by
        rw [← hgen]
        refine sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
          (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr ?_))
        rw [hg, mul_assoc, ← hab, ← mul_assoc]
      exact mem_centralizer_singleton_iff.mp (hle (mem_top y))
    have hnorm : A.Normal := ⟨fun n hn y => by
      rw [hAz] at hn ⊢
      obtain ⟨k, rfl⟩ := hn
      have hc : Commute y (a ^ k) := Commute.zpow_right (show Commute y a from hcent y) k
      rw [hc.eq, mul_inv_cancel_right]
      exact zpow_mem (mem_zpowers a) k⟩
    apply hAbot
    rw [eq_bot_iff, ← hO]
    exact le_oTwo (h.isPGroup.to_le h.le_S)
  obtain ⟨e₁⟩ := CFSG.Quasithin.RonanF95.nonempty_mulEquiv_dihedral hm3 ha hb2
    (rfl : orderOf (a * b) = m)
  have hcl : closure ({a, b} : Set H) = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine sup_le (zpowers_le.mpr (subset_closure (by simp))) (zpowers_le.mpr ?_)
    rw [hg]
    exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  have hcardH : Nat.card H = 2 * m := by
    have := Nat.card_congr e₁.toEquiv
    rwa [hcl, card_top, DihedralGroup.nat_card] at this
  have hmodd : ¬ 2 ∣ m := by
    have := index_mul_card S
    rw [hS2, hcardH, mul_comm 2 m] at this
    rw [← Nat.eq_of_mul_eq_mul_right two_pos this]
    exact h.not_dvd_index
  have hstar' : ∀ U : Subgroup H, a ∈ U → U ⊔ D = ⊤ → U = ⊤ := fun U haU hUD =>
    hstar U (by rw [← hAS, hAz]; exact zpowers_le.mpr haU) hUD
  have hmr : m = r ^ m.primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd (orderOf_pos g).ne' fun hd hdm =>
      eq_of_prime_dvd_orderOf ha hag hgen hmodd hr hQ hstar' hd hdm
  set t := m.primeFactorsList.length with ht
  have ht1 : 1 ≤ t := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, pow_zero] at hmr
    omega
  refine ⟨r, t, hr, hr2, ht1, ?_⟩
  rw [hmr] at e₁
  obtain ⟨e₂⟩ := nonempty_quotient_oTwo_mulEquiv_of_mulEquiv (Subgroup.topEquiv (G := H))
  exact ⟨e₂.trans ((QuotientGroup.quotientMulEquivOfEq hO).trans
    (QuotientGroup.quotientBot.trans
      (Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr hcl.symm).trans e₁))))⟩

theorem exists_hyperplane_conj_not_mem (h : Hyp24 S M A) {N : Subgroup H} [hNn : N.Normal]
    (hNc : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (hcop : Nat.Coprime 2 (Nat.card N))
    (hMN : M ⊔ N = ⊤) :
    ∃ B : Subgroup H, B ≤ A ∧ Nat.card A = 2 * Nat.card B ∧
      ∃ c ∈ N ⊓ centralizer (B : Set H), ∃ a ∈ A, c⁻¹ * (a * c * a⁻¹) ∉ M := by
  have hAbot : A ≠ ⊥ := fun hA => h.not_le_normalCore (by rw [hA]; exact bot_le)
  have hcardA : 2 ≤ Nat.card A := (one_lt_card_iff_ne_bot A).mpr hAbot
  have hAN : A ≤ normalizer (N : Set H) := by
    rw [normalizer_eq_top_iff.mpr hNn]
    exact le_top
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_hyperplanes Nat.prime_two
    h.elemAb hcardA hAN hcop
  by_contra hall
  push Not at hall
  apply h.not_le_normalCore
  intro a ha
  have haM : a ∈ M := h.le_M (h.le_S ha)
  have hconjN : ∀ c ∈ N, a * c * a⁻¹ ∈ N := fun c hc => hNn.conj_mem c hc a
  let K : Subgroup H :=
    { carrier := {c | c ∈ N ∧ c⁻¹ * (a * c * a⁻¹) ∈ M}
      mul_mem' := by
        rintro x y ⟨hxN, hxM⟩ ⟨hyN, hyM⟩
        refine ⟨N.mul_mem hxN hyN, ?_⟩
        have e : (x * y)⁻¹ * (a * (x * y) * a⁻¹) =
            y⁻¹ * (x⁻¹ * (a * x * a⁻¹)) * (a * y * a⁻¹) := by group
        rw [e, hNc y⁻¹ (N.inv_mem hyN) _ (N.mul_mem (N.inv_mem hxN) (hconjN x hxN)), mul_assoc]
        exact M.mul_mem hxM hyM
      one_mem' := ⟨N.one_mem, by simp⟩
      inv_mem' := by
        rintro x ⟨hxN, hxM⟩
        refine ⟨N.inv_mem hxN, ?_⟩
        have e : x⁻¹⁻¹ * (a * x⁻¹ * a⁻¹) = x * (a * x * a⁻¹)⁻¹ := by group
        rw [e, hNc x hxN _ (N.inv_mem (hconjN x hxN)),
          show (a * x * a⁻¹)⁻¹ * x = (x⁻¹ * (a * x * a⁻¹))⁻¹ by group]
        exact M.inv_mem hxM }
  have hNK : N ≤ K := by
    rw [← hgen]
    exact iSup₂_le fun B hB c hc => ⟨hc.1, hall B hB.1 hB.2 c hc a ha⟩
  rw [mem_normalCore_iff]
  intro g
  have hg : g ∈ ((M ⊔ N : Subgroup H) : Set H) := by
    rw [hMN]
    exact mem_top g
  rw [mul_normal] at hg
  obtain ⟨m, hm, c, hc, hmc⟩ := hg
  have hmc : m * c = g := hmc
  subst hmc
  have h1 : c * a * c⁻¹ ∈ M := by
    have h2 : c⁻¹⁻¹ * (a * c⁻¹ * a⁻¹) ∈ M := (hNK (N.inv_mem hc)).2
    have h3 := M.mul_mem h2 haM
    rwa [show c⁻¹⁻¹ * (a * c⁻¹ * a⁻¹) * a = c * a * c⁻¹ by group] at h3
  have := M.mul_mem (M.mul_mem hm h1) (M.inv_mem hm)
  rwa [show m * (c * a * c⁻¹) * m⁻¹ = m * c * a * (m * c)⁻¹ by group] at this

theorem isL24_zpowers_sup (h : Hyp24 S M A) {B : Subgroup H} (hBA : B ≤ A)
    (hidx : B.relIndex A = 2) {a y : H} (haA : a ∈ A) (haB : a ∉ B)
    (hyB : y ∈ centralizer (B : Set H)) (hay : a * y * a⁻¹ = y⁻¹) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hyp : orderOf y = p) (hyM : y ∉ M) : IsL24 S M A (zpowers y ⊔ A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  set L := zpowers y ⊔ A with hLdef
  have ha2 : a * a = 1 := by rw [← pow_two]; exact h.elemAb.2 a haA
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hAc : ∀ s ∈ A, ∀ t ∈ A, s * t = t * s := fun s hs t ht => isElemAbelian_comm h.elemAb hs ht
  have hBy : ∀ b ∈ B, b * y = y * b := fun b hb => mem_centralizer_iff.mp hyB b hb
  have hAy : ∀ t ∈ A, t * y * t⁻¹ = y ∨ t * y * t⁻¹ = y⁻¹ := by
    intro t ht
    rcases mem_or_inv_mul_mem hidx haA haB ht with htB | htB
    · left
      rw [hBy t htB, mul_inv_cancel_right]
    · right
      have e : t * y * t⁻¹ = a * ((a⁻¹ * t) * y * (a⁻¹ * t)⁻¹) * a⁻¹ := by group
      rw [e, hBy _ htB, mul_inv_cancel_right, hay]
  have hAN : A ≤ normalizer ((zpowers y : Subgroup H) : Set H) :=
    le_normalizer_zpowers fun t ht => by
      rcases hAy t ht with h1 | h1 <;> rw [h1]
      · exact mem_zpowers y
      · exact inv_mem (mem_zpowers y)
  have hLmem : ∀ x ∈ L, ∃ j : ℤ, ∃ t ∈ A, y ^ j * t = x := by
    intro x hx
    have hx' : x ∈ ((L : Subgroup H) : Set H) := hx
    rw [hLdef, coe_mul_of_right_le_normalizer_left _ _ hAN] at hx'
    obtain ⟨_, ⟨j, rfl⟩, t, ht, hjt⟩ := hx'
    exact ⟨j, t, ht, hjt⟩
  have hyL : y ∈ L := mem_sup_left (mem_zpowers y)
  have hAL : A ≤ L := le_sup_right
  obtain ⟨n, hn⟩ := (h.isPGroup.to_le h.le_S).exists_card_eq
  have hcardy : Nat.card (zpowers y) = p := by rw [Nat.card_zpowers, hyp]
  have hcardL : Nat.card L = p * Nat.card A := by
    apply le_antisymm
    · calc Nat.card L = Nat.card (((zpowers y : Subgroup H) : Set H) * (A : Set H)) := by
            rw [← coe_mul_of_right_le_normalizer_left _ _ hAN]
            rfl
        _ ≤ Nat.card ((zpowers y : Subgroup H) : Set H) * Nat.card (A : Set H) :=
            Set.natCard_mul_le
        _ = p * Nat.card A := by
            rw [← hcardy]
            rfl
    · apply Nat.le_of_dvd Nat.card_pos
      refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ ?_ ?_
      · rw [hn]
        exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
      · rw [← hcardy]
        exact card_dvd_of_le le_sup_left
      · exact card_dvd_of_le le_sup_right
  have hrelA : A.relIndex L = p := by
    have := relIndex_mul_card A L
    rw [inf_of_le_left hAL, hcardL] at this
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos this
  refine ⟨hAL, fun hle => hyM (hle hyL), ?_, ?_, ?_⟩
  ·
    rw [← inf_relIndex_right]
    intro hd
    have := hd.trans (relIndex_dvd_of_le_left L (le_inf h.le_S hAL))
    rw [hrelA] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp this).symm
  ·
    intro x hx hxM
    obtain ⟨j, t, ht, rfl⟩ := hLmem x hx
    apply le_antisymm (sup_le hAL (map_conj_le hAL hx))
    rw [hLdef]
    refine sup_le ?_ le_sup_left
    rw [zpowers_le]
    set K := A ⊔ A.map (MulAut.conj (y ^ j * t)).toMonoidHom with hK
    have hconj : (y ^ j * t) * a * (y ^ j * t)⁻¹ = y ^ (2 * j) * a := by
      have h1 : t * a * t⁻¹ = a := by rw [hAc t ht a haA, mul_inv_cancel_right]
      have h2 : a * y ^ (-j) * a⁻¹ = y ^ j := by rw [← conj_zpow, hay, inv_zpow', neg_neg]
      calc (y ^ j * t) * a * (y ^ j * t)⁻¹ = y ^ j * (t * a * t⁻¹) * y ^ (-j) := by group
        _ = y ^ j * (a * y ^ (-j) * a⁻¹) * a := by rw [h1]; group
        _ = y ^ (2 * j) * a := by rw [h2, ← zpow_add, two_mul]
    have hy2j : y ^ (2 * j) ∈ K := by
      have h1 : (y ^ j * t) * a * (y ^ j * t)⁻¹ ∈ K :=
        mem_sup_right (mem_map_conj.mpr ⟨a, haA, rfl⟩)
      rw [hconj] at h1
      have := K.mul_mem h1 (K.inv_mem (mem_sup_left haA : a ∈ K))
      rwa [mul_inv_cancel_right] at this
    have hyj : y ^ j ∉ M := fun hyjM => hxM (M.mul_mem hyjM (h.le_M (h.le_S ht)))
    have hne : y ^ (2 * j) ≠ 1 := by
      intro h1
      rw [← orderOf_dvd_iff_zpow_eq_one, hyp] at h1
      rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd h1 with h2 | h2
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (by exact_mod_cast h2))
      · apply hyj
        rw [orderOf_dvd_iff_zpow_eq_one.mp (by rwa [hyp])]
        exact M.one_mem
    have hord : orderOf (y ^ (2 * j)) = p := by
      refine orderOf_eq_prime ?_ hne
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hyp,
        pow_orderOf_eq_one, one_zpow]
    have hzeq : zpowers (y ^ (2 * j)) = zpowers y := by
      refine eq_of_le_of_card_ge (zpowers_le.mpr (zpow_mem (mem_zpowers y) _)) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hord, hyp]
    have hyz : y ∈ zpowers (y ^ (2 * j)) := by
      rw [hzeq]
      exact mem_zpowers y
    exact (zpowers_le.mpr hy2j) hyz
  ·
    set P := oTwo ↥L with hPdef
    set yL : L := ⟨y, hyL⟩ with hyLdef
    set aL : L := ⟨a, hAL haA⟩ with haLdef
    have hLB : L ≤ centralizer (B : Set H) := by
      rw [hLdef]
      refine sup_le (zpowers_le.mpr hyB) fun t ht => mem_centralizer_iff.mpr fun b hb => ?_
      exact hAc b (hBA hb) t ht
    have hBn : (B.subgroupOf L).Normal := ⟨fun n hn l => by
      rw [mem_subgroupOf] at hn ⊢
      have hc := mem_centralizer_iff.mp (hLB l.2) n hn
      rw [coe_mul, coe_mul, ← hc, coe_inv, mul_inv_cancel_right]
      exact hn⟩
    have hBP : B.subgroupOf L ≤ P :=
      le_oTwo (h.isPGroup.to_le (hBA.trans h.le_S)).comap_subtype
    have hyodd : ¬ 2 ∣ orderOf yL := by
      rw [hyLdef, Subgroup.orderOf_mk, hyp]
      intro hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hd).symm
    have hyP : yL ∉ P := fun hyP => by
      have h1 := eq_one_of_mem_oTwo hyP hyodd
      apply hyM
      rw [show y = 1 from congrArg Subtype.val h1]
      exact M.one_mem
    have haP : aL ∉ P := by
      intro haP
      have h1 : yL * aL * yL⁻¹ * aL⁻¹ ∈ P :=
        P.mul_mem ((inferInstance : P.Normal).conj_mem aL haP yL) (P.inv_mem haP)
      have h2 : yL * aL * yL⁻¹ * aL⁻¹ = yL ^ 2 := by
        apply Subtype.ext
        simp only [hyLdef, haLdef, coe_mul, coe_inv, coe_pow]
        calc y * a * y⁻¹ * a⁻¹ = y * (a * y * a⁻¹)⁻¹ := by group
          _ = y ^ 2 := by rw [hay, inv_inv, pow_two]
      rw [h2] at h1
      have h3 := eq_one_of_mem_oTwo h1 fun hd => hyodd (hd.trans (orderOf_pow_dvd 2))
      have h4 : orderOf yL ∣ 2 := orderOf_dvd_of_pow_eq_one h3
      rw [hyLdef, Subgroup.orderOf_mk, hyp] at h4
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h4)
    set ab : ↥L ⧸ P := (aL : ↥L ⧸ P) with habdef
    set yb : ↥L ⧸ P := (yL : ↥L ⧸ P) with hybdef
    have haa : ab * ab = 1 := by
      rw [habdef, ← QuotientGroup.mk_mul, show aL * aL = 1 from Subtype.ext ha2,
        QuotientGroup.mk_one]
    have hayay : ab * yb * (ab * yb) = 1 := by
      rw [habdef, hybdef, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      have e : aL * yL * (aL * yL) = 1 := by
        apply Subtype.ext
        simp only [hyLdef, haLdef, coe_mul, coe_one]
        calc a * y * (a * y) = a * y * a⁻¹ * y := by rw [hai]; group
          _ = 1 := by rw [hay, inv_mul_cancel]
      rw [e, QuotientGroup.mk_one]
    have hyb1 : yb ≠ 1 := fun h1 => hyP ((QuotientGroup.eq_one_iff _).mp h1)
    have hybp : yb ^ p = 1 := by
      rw [hybdef, ← QuotientGroup.mk_pow,
        show yL ^ p = 1 from Subtype.ext (by simp [hyLdef, ← hyp, pow_orderOf_eq_one]),
        QuotientGroup.mk_one]
    have hord : orderOf (ab * (ab * yb)) = p := by
      rw [← mul_assoc, haa, one_mul]
      exact orderOf_eq_prime hybp hyb1
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have hcl : closure ({ab, ab * yb} : Set (↥L ⧸ P)) = ⊤ := by
      rw [eq_top_iff]
      rintro z -
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
      obtain ⟨j, t, ht, hl⟩ := hLmem l l.2
      have hybc : yb ∈ closure ({ab, ab * yb} : Set (↥L ⧸ P)) := by
        have := mul_mem (inv_mem (subset_closure (by simp) :
          ab ∈ closure ({ab, ab * yb} : Set (↥L ⧸ P))))
          (subset_closure (by simp) : ab * yb ∈ closure ({ab, ab * yb} : Set (↥L ⧸ P)))
        rwa [inv_mul_cancel_left] at this
      have hl' : l = yL ^ j * ⟨t, hAL ht⟩ := Subtype.ext (by simp [hyLdef, hl])
      rw [hl', QuotientGroup.mk_mul, QuotientGroup.mk_zpow]
      refine mul_mem (zpow_mem hybc j) ?_
      rcases mem_or_inv_mul_mem hidx haA haB ht with htB | htB
      · have h1 : ((⟨t, hAL ht⟩ : L) : ↥L ⧸ P) = 1 :=
          (QuotientGroup.eq_one_iff _).mpr (hBP (by rw [mem_subgroupOf]; exact htB))
        rw [h1]
        exact one_mem _
      · have h1 : ((⟨a⁻¹ * t, hAL (mul_mem (inv_mem haA) ht)⟩ : L) : ↥L ⧸ P) = 1 :=
          (QuotientGroup.eq_one_iff _).mpr (hBP (by rw [mem_subgroupOf]; exact htB))
        have h2 : (⟨t, hAL ht⟩ : L) = aL * ⟨a⁻¹ * t, hAL (mul_mem (inv_mem haA) ht)⟩ :=
          Subtype.ext (by simp [haLdef])
        rw [h2, QuotientGroup.mk_mul, h1, mul_one]
        exact subset_closure (by simp [habdef])
    obtain ⟨e⟩ := CFSG.Quasithin.RonanF95.nonempty_mulEquiv_dihedral hp3 haa hayay hord
    refine ⟨p, 1, hp, hp2, le_rfl, ?_⟩
    rw [pow_one]
    exact ⟨Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr hcl.symm).trans e)⟩

theorem exists_isL24_of_normalCore_eq_bot [Group.IsSolvable H] (h : Hyp24 S M A)
    (hO : oTwo H = ⊥) (hD : M.normalCore = ⊥) : ∃ L, IsL24 S M A L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial H := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    exact h.isCoatom.1 (Subsingleton.elim _ _)
  obtain ⟨N, hNn, hNbot, -, p, k, hp, -, hNel, hNcard⟩ :=
    CFSG.SignalizerFunctor.Helpers.solvable_minimal_normal_exists (GroupType := H)
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
  have hyp : orderOf y = p := by
    have : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime (hNel.2 y hyN) hy1
  exact ⟨_, isL24_zpowers_sup h hBA hidx haA haB hyB hay hp hp2 hyp hy⟩

end Steps

theorem exists_isL24_aux (n : ℕ) : ∀ (H : Type u) [Group H] [Finite H] [Group.IsSolvable H],
    Nat.card H = n → ∀ {S M A : Subgroup H}, Hyp24 S M A → ∃ L, IsL24 S M A L := by
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro H _ _ _ hn S M A h
  have ih : IH24.{u} (Nat.card H) := fun G _ _ _ hG S' M' A' h' =>
    ihn _ (hn ▸ hG) G rfl h'
  by_cases hO : oTwo H = ⊥
  swap
  · exact exists_isL24_of_oTwo_ne_bot ih h hO
  by_cases hU : ∃ U : Subgroup H, S ≤ U ∧ U ⊔ M.normalCore = ⊤ ∧ U ≠ ⊤
  · obtain ⟨U, hSU, hUD, hU⟩ := hU
    exact exists_isL24_of_sup_normalCore ih h hSU hUD hU
  have hstar : ∀ U : Subgroup H, S ≤ U → U ⊔ M.normalCore = ⊤ → U = ⊤ := by
    intro U hSU hUD
    by_contra hU'
    exact hU ⟨U, hSU, hUD, hU'⟩
  by_cases hD : M.normalCore = ⊥
  · exact exists_isL24_of_normalCore_eq_bot h hO hD
  have hcard : Nat.card (H ⧸ M.normalCore) < Nat.card H := by
    rw [card_eq_card_quotient_mul_card_subgroup M.normalCore]
    have h1 : 1 < Nat.card M.normalCore := (one_lt_card_iff_ne_bot _).mpr hD
    have h2 := Nat.card_pos (α := H ⧸ M.normalCore)
    nlinarith
  obtain ⟨Lb, hLb⟩ := ih _ hcard (h.map_quotient M.normalCore (normalCore_le M))
  by_cases hL₁ : Lb.comap (QuotientGroup.mk' M.normalCore) = ⊤
  · exact ⟨⊤, isL24_top_of_comap_eq_top h hO hstar hLb hL₁⟩
  · exact exists_isL24_of_comap_ne_top ih h (inf_normalCore_eq_bot h hO hstar)
      (odd_card_normalCore h hO hstar) hLb hL₁

theorem exists_isL24_of_isSolvable {H : Type u} [Group H] [Finite H] [Group.IsSolvable H]
    {S M A : Subgroup H} (hS : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index) (hM : IsCoatom M)
    (hSM : S ≤ M) (hAS : A ≤ S) (hA : CFSG.Open.IsElemAbelian 2 A)
    (hAD : ¬ A ≤ M.normalCore) : ∃ L, IsL24 S M A L :=
  exists_isL24_aux _ H rfl ⟨hS, hSi, hM, hSM, hAS, hA, hAD⟩

theorem exists_isL24_of_isSolvable_subgroup {G : Type u} [Group G] [Finite G] {H : Subgroup G}
    [Group.IsSolvable H] {S M A : Subgroup G} (hS : IsPGroup 2 S) (hSH : S ≤ H)
    (hSi : ¬ 2 ∣ S.relIndex H) (hMH : M ≤ H) (hM : IsCoatom (M.subgroupOf H)) (hSM : S ≤ M)
    (hAS : A ≤ S) (hA : CFSG.Open.IsElemAbelian 2 A)
    (hAD : ∃ h ∈ H, ∃ a ∈ A, h * a * h⁻¹ ∉ M) : ∃ L ≤ H, IsL24 S M A L := by
  have hAH : A ≤ H := hAS.trans hSH
  have hcore : ¬ A.subgroupOf H ≤ (M.subgroupOf H).normalCore := by
    intro hle
    obtain ⟨g, hg, a, ha, hgaM⟩ := hAD
    have := mem_normalCore_iff.mp (hle (show (⟨a, hAH ha⟩ : H) ∈ A.subgroupOf H from ha))
      ⟨g, hg⟩
    rw [mem_subgroupOf] at this
    exact hgaM this
  obtain ⟨L', hL'⟩ := exists_isL24_of_isSolvable (H := H) (S := S.subgroupOf H)
    (M := M.subgroupOf H) (A := A.subgroupOf H) hS.comap_subtype hSi hM (fun _ hx => hSM hx)
    (fun _ hx => hAS hx) (isElemAbelian_subgroupOf hA) hcore
  exact ⟨_, map_subtype_le L', hL'.map_subtype hAH⟩

end CFSG.RankThree.S4Free.Stell
