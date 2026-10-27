module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofXNormal
public import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofGenTools
import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.LowTwoRank (StatedSp StatedProj)
open CFSG.Assembly.RankThreeEven (localRank projSp)

namespace Item812Res3

section Pure

variable {Q : Type} [Group Q]

theorem isElemAbelian_zpowers {u : Q} (hu : u ^ 3 = 1) :
    CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers u) := CFSG.Open.isElemAbelian_zpowers hu

theorem card_sup_zpowers_eq_sq [Finite Q] {p : ℕ} (hp : p.Prime) {u₁ u₂ : Q} (h1 : u₁ ^ p = 1)
    (h1' : u₁ ≠ 1) (h2 : u₂ ^ p = 1) (h2' : u₂ ∉ Subgroup.zpowers u₁)
    (hc : u₁ * u₂ = u₂ * u₁) :
    Nat.card (Subgroup.zpowers u₁ ⊔ Subgroup.zpowers u₂ : Subgroup Q) = p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hu₂1 : u₂ ≠ 1 := fun h => h2' (h ▸ Subgroup.one_mem _)
  have ho1 : orderOf u₁ = p := orderOf_eq_prime h1 h1'
  have ho2 : orderOf u₂ = p := orderOf_eq_prime h2 hu₂1
  have hinf : Subgroup.zpowers u₁ ⊓ Subgroup.zpowers u₂ = ⊥ := by
    have hcard : Nat.card (Subgroup.zpowers u₂) = p := by rw [Nat.card_zpowers, ho2]
    have : Fact (Nat.card (Subgroup.zpowers u₂)).Prime := ⟨by rw [hcard]; exact hp⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card ((Subgroup.zpowers u₁ ⊓
        Subgroup.zpowers u₂).subgroupOf (Subgroup.zpowers u₂)) with h | h
    · rw [Subgroup.subgroupOf_eq_bot] at h
      have h' := disjoint_iff.1 h
      rwa [inf_assoc, inf_idem] at h'
    · exfalso
      have hmem : (⟨u₂, Subgroup.mem_zpowers _⟩ : Subgroup.zpowers u₂) ∈
          (Subgroup.zpowers u₁ ⊓ Subgroup.zpowers u₂).subgroupOf (Subgroup.zpowers u₂) := by
        rw [h]
        exact Subgroup.mem_top _
      exact h2' (Subgroup.mem_subgroupOf.1 hmem).1
  have hcomm : ∀ x ∈ Subgroup.zpowers u₁, ∀ y ∈ Subgroup.zpowers u₂, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (show Commute u₁ u₂ from hc) i j).eq
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, ho1, ho2] at hcard
  rw [hcard, sq]

theorem isElemAbelian_sup_zpowers [Finite Q] {u₁ u₂ : Q} (h1 : u₁ ^ 3 = 1) (h2 : u₂ ^ 3 = 1)
    (hc : u₁ * u₂ = u₂ * u₁) :
    CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers u₁ ⊔ Subgroup.zpowers u₂ : Subgroup Q) := by
  refine Item812Res2.isElemAbelian_sup_of_commute (isElemAbelian_zpowers h1)
    (isElemAbelian_zpowers h2) ?_
  intro x hx y hy
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact (Commute.zpow_zpow (show Commute u₁ u₂ from hc) i j).eq

end Pure

theorem mem_normalizer_of_forall_commute {G : Type*} [Group G] {L : Subgroup G} {g : G}
    (hg : ∀ y ∈ L, g * y = y * g) : g ∈ Subgroup.normalizer (L : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    rw [hg w hw, mul_inv_cancel_right]
    exact hw
  · intro hw
    have h1 := hg _ hw
    have h2 : w = g * w * g⁻¹ := by
      calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
        _ = g⁻¹ * ((g * w * g⁻¹) * g) := by group
        _ = g⁻¹ * (g * (g * w * g⁻¹)) := by rw [h1]
        _ = g * w * g⁻¹ := by group
    rw [h2]
    exact hw

theorem mem_normalizer_map_of_mem_normalizer {M Q : Type*} [Group M] [Group Q] (ι : M →* Q)
    {V : Subgroup M} {s : M} (hs : s ∈ Subgroup.normalizer (V : Set M)) :
    ι s ∈ Subgroup.normalizer ((V.map ι : Subgroup Q) : Set Q) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hs ⊢
  have hcomp : ((MulAut.conj (ι s) : MulAut Q) : Q →* Q).comp ι =
      ι.comp ((MulAut.conj s : MulAut M) : M →* M) := by
    ext m
    simp [MulAut.conj_apply, map_mul, map_inv]
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hs]

theorem mem_normalizer_of_commute_perfect {G : Type} [Group G] [Finite G] {e g : G}
    {L P : Subgroup G} (hL : L ∈ thetaComponentsAt 3 e)
    (hg : g ∈ Subgroup.centralizer ({e} : Set G)) (hP : P ≠ ⊥) (hPperf : Group.IsPerfect P)
    (hPL : P ≤ L) (hPg : ∀ y ∈ P, g * y = y * g) :
    g ∈ Subgroup.normalizer (L : Set G) := by
  set H := Subgroup.centralizer ({e} : Set G) with hH
  obtain ⟨L₀, hL₀, rfl⟩ := hL
  set σ : MulAut H := MulAut.conj ⟨g, hg⟩ with hσ
  have hL₀' := map_mulEquiv_mem_thetaComponents Nat.prime_three σ hL₀
  have hPH : P ≤ H := hPL.trans (Subgroup.map_subtype_le L₀)
  set P₀ := P.subgroupOf H with hP₀
  have hP₀map : P₀.map H.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPH
  have hP₀ne : P₀ ≠ ⊥ := by
    intro h0
    apply hP
    rw [← hP₀map, h0, Subgroup.map_bot]
  have hP₀perf : Group.IsPerfect P₀ :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hPH).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have hP₀L : P₀ ≤ L₀ := by
    intro y hy
    have hy' : (y : G) ∈ L₀.map H.subtype := hPL (Subgroup.mem_subgroupOf.mp hy)
    obtain ⟨w, hw, hwy⟩ := hy'
    have : w = y := Subtype.ext hwy
    rwa [← this]
  have hP₀L' : P₀ ≤ L₀.map σ.toMonoidHom := by
    intro y hy
    refine ⟨y, hP₀L hy, ?_⟩
    apply Subtype.ext
    change g * (y : G) * g⁻¹ = y
    rw [hPg _ (Subgroup.mem_subgroupOf.mp hy), mul_inv_cancel_right]
  have heq := theta_component_eq_of_perfect_le Nat.prime_three hL₀ hL₀' hP₀ne hP₀perf hP₀L hP₀L'
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change (L₀.map H.subtype).map (MulAut.conj g).toMonoidHom = L₀.map H.subtype
  have hconj : (L₀.map H.subtype).map (MulAut.conj g).toMonoidHom =
      (L₀.map σ.toMonoidHom).map H.subtype := by
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  rw [hconj, ← heq]

theorem four_le_localRank_of_centralizes {Q : Type} [Group Q] [Finite Q] {M : Type*} [Group M]
    (hZ : Subgroup.center M = ⊥) {K : Subgroup Q} (ψ : M ≃* K) {s₁ s₂ : M}
    (hs₁ : s₁ ^ 3 = 1) (hs₁' : s₁ ≠ 1) (hs₂ : s₂ ^ 3 = 1) (hs₂' : s₂ ∉ Subgroup.zpowers s₁)
    (hs : s₁ * s₂ = s₂ * s₁) {V : Subgroup M} (hV3 : ¬ 3 ∣ Nat.card V) (hV2 : 2 ∣ Nat.card V)
    (hV₁ : s₁ ∈ Subgroup.normalizer (V : Set M)) (hV₂ : s₂ ∈ Subgroup.normalizer (V : Set M))
    {F : Subgroup Q} (hF : CFSG.Assembly.IsElemAbelian 3 F) (hF9 : Nat.card F = 9)
    (hFK : ∀ f ∈ F, ∀ k ∈ K, f * k = k * f) : 4 ≤ localRank 3 Q := by
  classical
  set ι : M →* Q := K.subtype.comp ψ.toMonoidHom with hι
  have hιinj : Function.Injective ι := K.subtype_injective.comp ψ.injective
  have hιK : ∀ m, ι m ∈ K := fun m => (ψ m).2
  have hu₁ : ι s₁ ^ 3 = 1 := by rw [← map_pow, hs₁, map_one]
  have hu₁' : ι s₁ ≠ 1 := fun h => hs₁' (hιinj (h.trans (map_one ι).symm))
  have hu₂ : ι s₂ ^ 3 = 1 := by rw [← map_pow, hs₂, map_one]
  have hu₂' : ι s₂ ∉ Subgroup.zpowers (ι s₁) := by
    rintro ⟨k, hk⟩
    apply hs₂'
    refine ⟨k, hιinj ?_⟩
    change ι (s₁ ^ k) = ι s₂
    rw [map_zpow]
    exact hk
  have hu : ι s₁ * ι s₂ = ι s₂ * ι s₁ := by rw [← map_mul, ← map_mul, hs]
  set S := Subgroup.zpowers (ι s₁) ⊔ Subgroup.zpowers (ι s₂) with hSdef
  have hS9 : Nat.card S = 3 ^ 2 :=
    card_sup_zpowers_eq_sq Nat.prime_three hu₁ hu₁' hu₂ hu₂' hu
  have hSK : S ≤ K := sup_le ((Subgroup.zpowers_le).mpr (hιK _))
    ((Subgroup.zpowers_le).mpr (hιK _))
  have hSab : CFSG.Assembly.IsElemAbelian 3 S := isElemAbelian_sup_zpowers hu₁ hu₂ hu
  have hFS : ∀ f ∈ F, ∀ s ∈ S, f * s = s * f := fun f hf s hs => hFK f hf s (hSK hs)
  have hinf : F ⊓ S = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxF, hxS⟩
    exact Item812Res2.eq_one_of_forall_mul_comm hZ ψ (hSK hxS) (fun y hy => hFK x hxF y hy)
  have hEcard : Nat.card (F ⊔ S : Subgroup Q) = 3 ^ 4 := by
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute F S hFS
    rw [hinf, Subgroup.card_bot, mul_one, hF9, hS9] at hcard
    rw [hcard]
    norm_num
  have hEab : CFSG.Assembly.IsElemAbelian 3 (F ⊔ S : Subgroup Q) :=
    Item812Res2.isElemAbelian_sup_of_commute hF hSab hFS
  set V' := V.map ι with hV'
  have hV'card : Nat.card V' = Nat.card V := Subgroup.card_map_of_injective hιinj
  have hV'K : V' ≤ K := by
    rintro _ ⟨v, -, rfl⟩
    exact hιK v
  have hFN : F ≤ Subgroup.normalizer (V' : Set Q) := fun f hf =>
    mem_normalizer_of_forall_commute fun y hy => hFK f hf y (hV'K hy)
  have hSN : S ≤ Subgroup.normalizer (V' : Set Q) :=
    sup_le ((Subgroup.zpowers_le).mpr (mem_normalizer_map_of_mem_normalizer ι hV₁))
      ((Subgroup.zpowers_le).mpr (mem_normalizer_map_of_mem_normalizer ι hV₂))
  refine CFSG.RankThree.Classical2.le_localRank_of_normalizes Nat.prime_three (sup_le hFN hSN)
    hEab hEcard ?_ (by rw [hV'card]; exact hV2)
  rw [hV'card]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hV3

@[expose] def IsYModel (M : Type*) [Group M] : Prop :=
  Subgroup.center M = ⊥ ∧ ∃ (s₁ s₂ : M) (V : Subgroup M), s₁ ^ 3 = 1 ∧ s₁ ≠ 1 ∧ s₂ ^ 3 = 1 ∧
    s₂ ∉ Subgroup.zpowers s₁ ∧ s₁ * s₂ = s₂ * s₁ ∧ ¬ 3 ∣ Nat.card V ∧ 2 ∣ Nat.card V ∧
    s₁ ∈ Subgroup.normalizer (V : Set M) ∧ s₂ ∈ Subgroup.normalizer (V : Set M)

theorem IsYModel.of_mulEquiv {M M' : Type*} [Group M] [Group M'] (e : M ≃* M')
    (hM : IsYModel M) : IsYModel M' := by
  obtain ⟨hZ, s₁, s₂, V, hs₁, hs₁', hs₂, hs₂', hs, hV3, hV2, hV₁, hV₂⟩ := hM
  refine ⟨?_, e s₁, e s₂, V.map e.toMonoidHom, by rw [← map_pow, hs₁, map_one], ?_,
    by rw [← map_pow, hs₂, map_one], ?_, by rw [← map_mul, ← map_mul, hs], ?_, ?_,
    mem_normalizer_map_of_mem_normalizer e.toMonoidHom hV₁,
    mem_normalizer_map_of_mem_normalizer e.toMonoidHom hV₂⟩
  · rw [eq_bot_iff]
    intro z hz
    have hz' : e.symm z ∈ Subgroup.center M := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro y
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hz (e y)
    rw [hZ, Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot]
    simpa using congrArg e hz'
  · intro h
    exact hs₁' (e.injective (h.trans (map_one e).symm))
  · rintro ⟨k, hk⟩
    apply hs₂'
    refine ⟨k, e.injective ?_⟩
    change e (s₁ ^ k) = e s₂
    rw [map_zpow]
    exact hk
  · rwa [Subgroup.card_map_of_injective e.injective]
  · rwa [Subgroup.card_map_of_injective e.injective]

section Alt

open Equiv

@[expose] def alt9S₁ : Perm (Fin 9) := swap 0 1 * swap 1 2
@[expose] def alt9S₂ : Perm (Fin 9) := swap 4 5 * swap 5 6
@[expose] def alt9D₁ : Perm (Fin 9) := swap 0 1 * swap 2 3
@[expose] def alt9D₂ : Perm (Fin 9) := swap 0 2 * swap 1 3

theorem alt9S₁_mem : alt9S₁ ∈ alternatingGroup (Fin 9) :=
  Perm.mem_alternatingGroup.mpr (by decide)
theorem alt9S₂_mem : alt9S₂ ∈ alternatingGroup (Fin 9) :=
  Perm.mem_alternatingGroup.mpr (by decide)
theorem alt9D₁_mem : alt9D₁ ∈ alternatingGroup (Fin 9) :=
  Perm.mem_alternatingGroup.mpr (by decide)
theorem alt9D₂_mem : alt9D₂ ∈ alternatingGroup (Fin 9) :=
  Perm.mem_alternatingGroup.mpr (by decide)

theorem isYModel_alternatingGroup_nine : IsYModel (alternatingGroup (Fin 9)) := by
  classical
  set s₁ : alternatingGroup (Fin 9) := ⟨alt9S₁, alt9S₁_mem⟩ with hs₁
  set s₂ : alternatingGroup (Fin 9) := ⟨alt9S₂, alt9S₂_mem⟩ with hs₂
  set d₁ : alternatingGroup (Fin 9) := ⟨alt9D₁, alt9D₁_mem⟩ with hd₁
  set d₂ : alternatingGroup (Fin 9) := ⟨alt9D₂, alt9D₂_mem⟩ with hd₂
  set V := Subgroup.zpowers d₁ ⊔ Subgroup.zpowers d₂ with hV
  have hd₂z : d₂ ∉ Subgroup.zpowers d₁ := by
    rw [mem_zpowers_iff_mem_range_orderOf]
    have hord : orderOf d₁ = 2 :=
      orderOf_eq_prime (Subtype.ext (by decide)) (fun h => by
        have := congrArg Subtype.val h
        revert this
        decide)
    rw [hord]
    intro hmem
    simp only [Finset.mem_image, Finset.mem_range] at hmem
    obtain ⟨k, hk, hkd⟩ := hmem
    interval_cases k
    · have := congrArg Subtype.val hkd
      revert this
      decide
    · have := congrArg Subtype.val hkd
      revert this
      decide
  have hV4 : Nat.card V = 2 ^ 2 :=
    card_sup_zpowers_eq_sq Nat.prime_two (Subtype.ext (by decide))
      (fun h => by
        have := congrArg Subtype.val h
        revert this
        decide)
      (Subtype.ext (by decide)) hd₂z (Subtype.ext (by decide))
  refine ⟨alternatingGroup.center_eq_bot (by simp), s₁, s₂, V, Subtype.ext (by decide),
    fun h => by
      have := congrArg Subtype.val h
      revert this
      decide,
    Subtype.ext (by decide), ?_, Subtype.ext (by decide), by rw [hV4]; norm_num,
    by rw [hV4]; norm_num, ?_, ?_⟩
  ·
    rintro ⟨k, hk⟩
    have h1 : (alt9S₁ ^ k) 4 = 4 :=
      Perm.zpow_apply_eq_self_of_apply_eq_self (by decide) k
    have h2 : ((s₁ ^ k : alternatingGroup (Fin 9)) : Perm (Fin 9)) = alt9S₂ :=
      congrArg Subtype.val hk
    rw [Subgroup.coe_zpow] at h2
    rw [h2] at h1
    revert h1
    decide
  ·
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hle : V.map ((MulAut.conj s₁ : MulAut (alternatingGroup (Fin 9))) :
        alternatingGroup (Fin 9) →* alternatingGroup (Fin 9)) ≤ V := by
      rw [hV, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        have h : (MulAut.conj s₁ : MulAut (alternatingGroup (Fin 9))) d₁ = d₁ * d₂ :=
          Subtype.ext (by simp only [MulAut.conj_apply]; decide)
        change (MulAut.conj s₁ : MulAut (alternatingGroup (Fin 9))) d₁ ∈ V
        rw [h]
        exact V.mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
      · rw [Subgroup.zpowers_le]
        have h : (MulAut.conj s₁ : MulAut (alternatingGroup (Fin 9))) d₂ = d₁ :=
          Subtype.ext (by simp only [MulAut.conj_apply]; decide)
        change (MulAut.conj s₁ : MulAut (alternatingGroup (Fin 9))) d₂ ∈ V
        rw [h]
        exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj s₁).injective])
  ·
    refine mem_normalizer_of_forall_commute fun y hy => ?_
    have hc : V ≤ Subgroup.centralizer ({s₂} : Set (alternatingGroup (Fin 9))) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact Subtype.ext (by decide)
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact Subtype.ext (by decide)
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hc hy)).symm

end Alt

section Sp

open CFSG.LieType.SteinbergBR.EvenSp
open scoped MatrixGroups

variable (F : Type) [Field F]

@[expose] noncomputable def sp6Plane (i : Fin 3) : SL(2, F) →* StatedSp 3 F :=
  ((planeHom.comp (MonoidHom.mulSingle (fun _ : Fin 3 => GL (Fin 2) F) i)).comp
      Matrix.SpecialLinearGroup.toGL).codRestrict (StatedSp 3 F) fun B =>
    planeHom_mem_statedSp _ fun j => by
      rw [MonoidHom.mulSingle_apply, Pi.mulSingle_apply]
      split_ifs
      · rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
        exact B.2
      · simp

variable {F}

theorem sp6Plane_injective (i : Fin 3) : Function.Injective (sp6Plane F i) := by
  intro B B' h
  have h1 := congrArg (fun g : StatedSp 3 F => (g : GL (Fin 3 ⊕ Fin 3) F)) h
  change planeHom (Pi.mulSingle i (Matrix.SpecialLinearGroup.toGL B)) =
    planeHom (Pi.mulSingle i (Matrix.SpecialLinearGroup.toGL B')) at h1
  exact Matrix.SpecialLinearGroup.toGL_injective
    (Pi.mulSingle_injective i (planeHom_injective h1))

theorem sp6Plane_commute {i j : Fin 3} (hij : i ≠ j) (B B' : SL(2, F)) :
    sp6Plane F i B * sp6Plane F j B' = sp6Plane F j B' * sp6Plane F i B := by
  apply Subtype.ext
  change planeHom (Pi.mulSingle i (Matrix.SpecialLinearGroup.toGL B)) *
      planeHom (Pi.mulSingle j (Matrix.SpecialLinearGroup.toGL B')) =
    planeHom (Pi.mulSingle j (Matrix.SpecialLinearGroup.toGL B')) *
      planeHom (Pi.mulSingle i (Matrix.SpecialLinearGroup.toGL B))
  rw [← map_mul, ← map_mul, (Pi.mulSingle_commute hij _ _).eq]

theorem sp6Plane_not_mem_zpowers (g h : SL(2, F)) (hh : h ≠ 1) :
    sp6Plane F 1 h ∉ Subgroup.zpowers (sp6Plane F 0 g) := by
  rintro ⟨k, hk⟩
  have hk' : sp6Plane F 0 (g ^ k) = sp6Plane F 1 h := by
    rw [map_zpow]
    exact hk
  have h1 := congrArg (fun x : StatedSp 3 F => (x : GL (Fin 3 ⊕ Fin 3) F)) hk'
  change planeHom (Pi.mulSingle 0 (Matrix.SpecialLinearGroup.toGL (g ^ k))) =
    planeHom (Pi.mulSingle 1 (Matrix.SpecialLinearGroup.toGL h)) at h1
  have h2 := congrFun (planeHom_injective h1) 1
  rw [Pi.mulSingle_eq_of_ne (show (1 : Fin 3) ≠ 0 by decide), Pi.mulSingle_eq_same] at h2
  apply hh
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [← h2, map_one]

theorem isYModel_statedSp_three [CharP F 2] : IsYModel (StatedSp 3 F) := by
  classical
  set D := KFacts.ordThreeSL F with hD
  set U := Item812Res2.unipSL F with hU
  have hD3 : D ^ 3 = 1 := KFacts.ordThreeSL_pow_three F
  have hD1 : D ≠ 1 := KFacts.ordThreeSL_ne_one F
  set j := sp6Plane F 2 U with hj
  have hj2 : j ^ 2 = 1 := by rw [hj, ← map_pow, Item812Res2.unipSL_sq, map_one]
  have hj1 : j ≠ 1 := fun h => Item812Res2.unipSL_ne_one F
    (sp6Plane_injective 2 (h.trans (map_one _).symm))
  have hjord : orderOf j = 2 := orderOf_eq_prime hj2 hj1
  have hcardV : Nat.card (Subgroup.zpowers j) = 2 := by rw [Nat.card_zpowers, hjord]
  refine ⟨CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot (by norm_num), sp6Plane F 0 D,
    sp6Plane F 1 D, Subgroup.zpowers j, by rw [← map_pow, hD3, map_one],
    fun h => hD1 (sp6Plane_injective 0 (h.trans (map_one _).symm)),
    by rw [← map_pow, hD3, map_one], sp6Plane_not_mem_zpowers D D hD1,
    sp6Plane_commute (by decide) D D, by rw [hcardV]; norm_num, by rw [hcardV],
    Item812Res2.mem_normalizer_zpowers_of_commute (sp6Plane_commute (by decide) D U),
    Item812Res2.mem_normalizer_zpowers_of_commute (sp6Plane_commute (by decide) D U)⟩

theorem isYModel_projSp_three_two : IsYModel (projSp 3 (GaloisField 2 1)) :=
  IsYModel.of_mulEquiv ((Sec4.projSpEquivStatedProj 3 (GaloisField 2 1)).trans
    (projEquiv (by norm_num))).symm isYModel_statedSp_three

end Sp

end Item812Res3

end CFSG.RankThree.PartTwo.Sec8
