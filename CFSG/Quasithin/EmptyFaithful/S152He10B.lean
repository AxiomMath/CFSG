module

public import CFSG.Quasithin.Background.C2PushA3
public import CFSG.Quasithin.Vol2.Ch1Chief
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.EmptyFaithful.S152He9A5
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.He10

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.He9
open scoped commutatorElement Pointwise

section Abstract

variable {X : Type*} [Group X] [Finite X]

theorem closure_not_dvd_three_eq_top_of_perfect {Q : Type*} [Group Q] [Finite Q]
    (hQ : Group.IsPerfect Q) : Subgroup.closure {x : Q | ¬ 3 ∣ orderOf x} = ⊤ := by
  set S : Set Q := {x : Q | ¬ 3 ∣ orderOf x} with hS
  have hNn : (Subgroup.closure S).Normal := by
    refine ⟨fun n hn g => ?_⟩
    refine Subgroup.closure_induction (p := fun n _ => g * n * g⁻¹ ∈ Subgroup.closure S) ?_ ?_ ?_ ?_ hn
    · intro x hx
      apply Subgroup.subset_closure
      show ¬ 3 ∣ orderOf (g * x * g⁻¹)
      have := (MulAut.conj g).orderOf_eq x
      rw [MulAut.conj_apply] at this
      rw [this]
      exact hx
    · simp
    · intro x y _ _ hx hy
      simpa [mul_assoc] using mul_mem hx hy
    · intro x _ hx
      have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [this]
      exact inv_mem hx
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : IsPGroup 3 (Q ⧸ Subgroup.closure S) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨a, b, hab, -, ha, hb⟩ := C2Push.exists_threePrime_threePart g
    obtain ⟨k, hk⟩ := hb b (Subgroup.mem_zpowers b)
    refine ⟨k, ?_⟩
    have h1 : (QuotientGroup.mk a : Q ⧸ Subgroup.closure S) = 1 :=
      (QuotientGroup.eq_one_iff a).mpr (Subgroup.subset_closure ha)
    have h2 : (QuotientGroup.mk g : Q ⧸ Subgroup.closure S) = QuotientGroup.mk b := by
      rw [← hab, QuotientGroup.mk_mul, h1, one_mul]
    rw [h2, ← QuotientGroup.mk_pow, hk]
    rfl
  have hperf : Group.IsPerfect (Q ⧸ Subgroup.closure S) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hsolv : Group.IsSolvable (Q ⧸ Subgroup.closure S) := by
    have : Group.IsNilpotent (Q ⧸ Subgroup.closure S) := h3.isNilpotent
    infer_instance
  have hsub : Subsingleton (Q ⧸ Subgroup.closure S) := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isSolvable (Q ⧸ Subgroup.closure S) hsolv
  rw [eq_top_iff]
  intro g _
  have : (QuotientGroup.mk g : Q ⧸ Subgroup.closure S) = 1 := Subsingleton.elim _ _
  exact (QuotientGroup.eq_one_iff g).mp this

theorem le_of_forall_eq_mul_prod_of_commute {K M₀ Q : Subgroup X}
    (hK : ⁅K, K⁆ = K) (hQ : IsPGroup 3 Q) {r : ℕ} (B : Fin r → Subgroup X)
    (hBQ : ∀ i, B i ≤ Q) (hcomm : ∀ i, ∀ x ∈ K, ∀ y ∈ B i, Commute x y)
    (hx : ∀ x ∈ K, ∃ m ∈ M₀, ∃ b : Fin r → X, (∀ i, b i ∈ B i) ∧ x = m * (List.ofFn b).prod) :
    K ≤ M₀ := by
  have hK3 := closure_not_dvd_three_eq_top_of_perfect (Subgroup.isPerfect_iff.mpr hK)
  have hle : Subgroup.closure {x : ↥K | ¬ 3 ∣ orderOf x} ≤ M₀.subgroupOf K := by
    rw [Subgroup.closure_le]
    intro x hx3
    have hx3' : ¬ 3 ∣ orderOf (x : X) := by
      rwa [Subgroup.orderOf_coe]
    obtain ⟨m, hm, b, hb, hxm⟩ := hx (x : X) x.2
    set f : X := (List.ofFn b).prod with hf
    have hfQ : f ∈ Q :=
      Subgroup.list_prod_mem _ fun y hy => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
        exact hBQ i (hb i)
    have hfk : ∃ k : ℕ, f ^ 3 ^ k = 1 := by
      obtain ⟨k, hk⟩ := hQ ⟨f, hfQ⟩
      exact ⟨k, congrArg Subtype.val hk⟩
    have hfc : Commute (x : X) f :=
      Commute.list_prod_right _ _ fun y hy => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
        exact hcomm i (x : X) x.2 (b i) (hb i)
    have hm' : m = (x : X) * f⁻¹ := by rw [hxm]; group
    have := C2Push.mem_zpowers_mul_inv_of_commute hfc hx3' hfk
    rw [← hm'] at this
    exact Subgroup.zpowers_le.mpr hm this
  intro y hy
  have hy' : (⟨y, hy⟩ : ↥K) ∈ Subgroup.closure {x : ↥K | ¬ 3 ∣ orderOf x} :=
    hK3 ▸ Subgroup.mem_top _
  exact hle hy'

end Abstract

section A36

variable {X : Type} [Group X] [Finite X]

theorem card_of_isElemAbelianOfRank' {V : Type*} [Group V] {p n : ℕ}
    (h : IsElemAbelianOfRank p n V) : Nat.card V = p ^ n := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin n →
    ZMod p) ≃ (Fin n → ZMod p)), Nat.card_pi]
  simp [Nat.card_zmod]

theorem commute_of_normal_threeGroup {L D : Subgroup X} (hL : A36Strong L) (hDL : D ≤ L)
    (hDn : (D.subgroupOf L).Normal) (hD3 : IsPGroup 3 D) : ∀ d ∈ D, ∀ l ∈ L, Commute d l := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hconc, -, -⟩ := hL
  set D' : Subgroup ↥L := D.subgroupOf L with hD'
  have hD'3 : IsPGroup 3 ↥D' := hD3.of_equiv (Subgroup.subgroupOfEquivOfLe hDL).symm
  have hnil : Group.IsNilpotent ↥D' := hD'3.isNilpotent
  have hDF : D' ≤ CFSG.fittingSubgroup ↥L := le_sSup ⟨hDn, hnil⟩
  have quasi : CFSG.IsQuasisimple ↥L → D' = ⊥ ∨ D' ≤ Subgroup.center ↥L := by
    intro hq
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hDn with h | h
    · exfalso
      have h3top : IsPGroup 3 ↥(⊤ : Subgroup ↥L) := h ▸ hD'3
      have h3L : IsPGroup 3 ↥L := h3top.of_equiv Subgroup.topEquiv
      have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hq
      have : Group.IsPerfect ↥L := hq.1
      have hsolv : Group.IsSolvable ↥L := by
        have : Group.IsNilpotent ↥L := h3L.isNilpotent
        infer_instance
      exact Group.IsPerfect.not_isSolvable ↥L hsolv
    · exact Or.inr h
  have key : D' = ⊥ ∨ D' ≤ Subgroup.center ↥L := by
    rcases hconc with ⟨hc, -, -⟩ | ⟨hc, -, -⟩ | h3 | h4
    · exact quasi hc.1
    · exact quasi hc.1
    · left
      obtain ⟨p, hp, hp3, -, hF, -⟩ := h3
      have hcard : Nat.card ↥(CFSG.fittingSubgroup ↥L) = p ^ 2 := card_of_isElemAbelianOfRank' hF
      have hdvd : Nat.card ↥D' ∣ p ^ 2 := hcard ▸ Subgroup.card_dvd_of_le hDF
      obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hD'3
      rw [ha] at hdvd
      have ha0 : a = 0 := by
        by_contra hne
        have h3p : 3 ∣ p ^ 2 := (dvd_pow_self 3 hne).trans hdvd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.prime_three.dvd_of_dvd_pow h3p)
        omega
      rw [ha0, pow_zero] at ha
      exact Subgroup.card_eq_one.mp ha
    · left
      obtain ⟨-, -, -, hprime⟩ := h4
      obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hD'3
      have ha0 : a = 0 := by
        by_contra hne
        have h3d : 3 ∣ Nat.card ↥(CFSG.fittingSubgroup ↥L) :=
          (ha ▸ dvd_pow_self 3 hne).trans (Subgroup.card_dvd_of_le hDF)
        have := (hprime 3 Nat.prime_three h3d).1
        omega
      rw [ha0, pow_zero] at ha
      exact Subgroup.card_eq_one.mp ha
  intro d hd l hl
  have hdL : d ∈ L := hDL hd
  have hd' : (⟨d, hdL⟩ : ↥L) ∈ D' := Subgroup.mem_subgroupOf.mpr hd
  rcases key with h | h
  · rw [h, Subgroup.mem_bot] at hd'
    have : d = 1 := congrArg Subtype.val hd'
    rw [this]
    exact Commute.one_left l
  · have := Subgroup.mem_center_iff.mp (h hd') ⟨l, hl⟩
    exact congrArg Subtype.val this.symm

def ThreeCentral {Z : Type*} [Group Z] (K : Subgroup Z) : Prop :=
  ∀ D : Subgroup Z, D ≤ K → (D.subgroupOf K).Normal → IsPGroup 3 D → ∀ d ∈ D, ∀ l ∈ K, Commute d l

theorem threeCentral_of_A36 {L : Subgroup X} (hL : A36Strong L) : ThreeCentral L :=
  fun _ hDL hDn hD3 => commute_of_normal_threeGroup hL hDL hDn hD3

theorem ThreeCentral.map {Z W : Type*} [Group Z] [Group W] {K : Subgroup Z} (e : Z ≃* W)
    (h : ThreeCentral K) : ThreeCentral (K.map e.toMonoidHom) := by
  intro D hD hDn hD3 d hd l hl
  set D₁ : Subgroup Z := D.map e.symm.toMonoidHom with hD₁
  have hmemD₁ : ∀ z, z ∈ D₁ ↔ e z ∈ D := by
    intro z
    rw [hD₁, Subgroup.mem_map_equiv]
    simp
  have hmemK : ∀ z, z ∈ K ↔ e z ∈ K.map e.toMonoidHom := by
    intro z
    rw [Subgroup.mem_map_equiv]
    simp
  have hD₁K : D₁ ≤ K := fun z hz => (hmemK z).mpr (hD ((hmemD₁ z).mp hz))
  have hKN : K.map e.toMonoidHom ≤ Subgroup.normalizer (D : Set W) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hD).mp hDn
  have hD₁n : (D₁.subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hD₁K]
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have h1 := Subgroup.mem_normalizer_iff.mp (hKN ((hmemK k).mp hk)) (e z)
    rw [hmemD₁, hmemD₁]
    simpa using h1
  have hD₁3 : IsPGroup 3 D₁ := by
    have : D₁ = D.map e.symm.toMonoidHom := rfl
    exact hD3.map e.symm.toMonoidHom |>.of_equiv
      (MulEquiv.subgroupCongr (by rfl : D₁ = D.map e.symm.toMonoidHom)).symm
  have hd' : e.symm d ∈ D₁ := by
    rw [hD₁, Subgroup.mem_map_equiv]
    simpa using hd
  have hl' : e.symm l ∈ K := by
    have := (hmemK (e.symm l)).mpr (by simpa using hl)
    exact this
  have := h D₁ hD₁K hD₁n hD₁3 (e.symm d) hd' (e.symm l) hl'
  have h2 := congrArg e this.eq
  simp only [map_mul, MulEquiv.apply_symm_apply] at h2
  exact h2

omit [Finite X] in
theorem commute_of_perfect_normal {K Q B : Subgroup X} (hK : ⁅K, K⁆ = K) [hKn : K.Normal]
    [hQn : Q.Normal] (hQ3 : IsPGroup 3 Q) (hB : B ≤ Q) (hA : ThreeCentral K) :
    ∀ x ∈ K, ∀ y ∈ B, Commute x y := by
  set D : Subgroup X := K ⊓ Q with hD
  have hDK : D ≤ K := inf_le_left
  have hDn : (D.subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hDK]
    intro k _
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer_of_normal (H := K) (K := ⊤) (Subgroup.mem_top k),
        Subgroup.le_normalizer_of_normal (H := Q) (K := ⊤) (Subgroup.mem_top k)⟩
  have hD3 : IsPGroup 3 D := hQ3.to_le inf_le_right
  have hDc := hA D hDK hDn hD3
  have hKB : ⁅K, B⁆ ≤ D := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    refine ⟨?_, ?_⟩
    · have : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact K.mul_mem hx (hKn.conj_mem _ (K.inv_mem hx) y)
    · have : ⁅x, y⁆ = (x * y * x⁻¹) * y⁻¹ := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact Q.mul_mem (hQn.conj_mem y (hB hy) x) (Q.inv_mem (hB hy))
  have hBK : ⁅B, K⁆ ≤ D := by
    rw [Subgroup.commutator_comm]
    exact hKB
  have hDK' : ∀ E : Subgroup X, E ≤ D → ⁅E, K⁆ = ⊥ := by
    intro E hE
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hDc a (hE ha) b hb)
  have h1 : ⁅⁅K, B⁆, K⁆ = ⊥ := hDK' _ hKB
  have h2 : ⁅⁅B, K⁆, K⁆ = ⊥ := hDK' _ hBK
  have h3 : ⁅⁅K, K⁆, B⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rw [hK] at h3
  intro x hx y hy
  have : ⁅x, y⁆ ∈ ⁅K, B⁆ := Subgroup.commutator_mem_commutator hx hy
  rw [h3, Subgroup.mem_bot] at this
  exact commutatorElement_eq_one_iff_mul_comm.mp this

end A36

section Assembly

variable {G : Type} [Group G] [Finite G]

theorem le_of_all_A3 (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h36 : A36ForSQTK) {G₀ R M₁ L : Subgroup G}
    (hyp : HypC23 G₀ R M₁) (hne : pCoreOf 2 G₀ ≠ ⊥) (hL : L ∈ cComp G₀)
    (hRL : R ≤ Subgroup.normalizer (L : Set G)) (hsyl : IsSylowTwoOf R (R ⊔ L))
    {r : ℕ} (Lb : Fin r → Subgroup G)
    (hLb : ∀ i, IsBlock2 (R ⊔ L) (Lb i) ∧ Nat.card (↥(Lb i) ⧸ CFSG.pCore 2 ↥(Lb i)) = 3)
    (hprod : ∀ h ∈ R ⊔ L, ∃ m ∈ M₁ ⊓ (R ⊔ L), ∃ x : Fin r → G,
      (∀ i, x i ∈ Lb i) ∧ h = m * (List.ofFn x).prod) : L ≤ M₁ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Y : Subgroup G := R ⊔ L with hY
  have hLG : L ≤ G₀ := le_of_mem_cComp hL
  have hRG : R ≤ G₀ := hyp.radical.1
  have hYG : Y ≤ G₀ := sup_le hRG hLG
  have hLY : L ≤ Y := le_sup_right
  have hRY : R ≤ Y := le_sup_left
  have hLY' : L ∈ cComp Y := cComp_mem_of_le hL hLY hYG
  have hOR : pCoreOf 2 Y ≤ R := B6.pCoreOf_two_le_of_isSylowTwoOf hsyl
  have hRM : R ≤ M₁ := fun x hx =>
    hyp.cgs (inf_normalizer_le_cgsIn hyp.radical.2.1 ⟨hRG hx, Subgroup.le_normalizer hx⟩)
  have hOY : pCoreOf 2 Y ≤ M₁ ⊓ Y := le_inf (hOR.trans hRM) (pCoreOf_le 2 Y)
  have hYne : pCoreOf 2 Y ≠ ⊥ := by
    intro hbot
    apply hne
    have hle : pCoreOf 2 G₀ ≤ pCoreOf 2 Y :=
      le_pCoreOf_of_le_normalizer ((c2_1_pCore_le hyp.radical).trans hRY)
        (hYG.trans (le_normalizer_pCoreOf 2 G₀)) (pCoreOf_isPGroup 2 G₀)
    exact le_bot_iff.mp (hbot ▸ hle)
  have hA36 : A36Strong (modO2Image Y L) := lemma_1_2_1_four_strong hK hs hnab h36 hYne hLY'
  have hTC : ThreeCentral (imageOTwoQuot Y L) := by
    let e : (↥Y ⧸ CFSG.pCore 2 ↥Y) ≃* OTwoQuot Y :=
      QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥Y 2)
    have hmap : imageOTwoQuot Y L = (modO2Image Y L).map e.toMonoidHom := by
      unfold imageOTwoQuot modO2Image
      rw [Subgroup.map_map]
      congr 1
    rw [hmap]
    exact (threeCentral_of_A36 hA36).map e
  have hYN : Y ≤ Subgroup.normalizer (L : Set G) := sup_le hRL Subgroup.le_normalizer
  have hKn : (imageOTwoQuot Y L).Normal := by
    have hn : (L.subgroupOf Y).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).mpr hYN
    exact hn.map _ (QuotientGroup.mk'_surjective _)
  have hKperf : ⁅imageOTwoQuot Y L, imageOTwoQuot Y L⁆ = imageOTwoQuot Y L := by
    obtain ⟨e⟩ := C2Push.nonempty_mulEquiv_pCore_quotient_imageOTwoQuot (subnormal_of_mem_cComp hLY')
    have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hL)
    have : Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
    have : Group.IsPerfect ↥(imageOTwoQuot Y L) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    exact Subgroup.isPerfect_iff.mp this
  have hB3 : ∀ i, IsPGroup 3 (imageOTwoQuot Y (Lb i)) := by
    intro i
    obtain ⟨e⟩ := C2Push.nonempty_mulEquiv_pCore_quotient_imageOTwoQuot (IsBlock2.isSubnormal (hLb i).1)
    have hcard : Nat.card ↥(imageOTwoQuot Y (Lb i)) = 3 ^ 1 :=
      ((Nat.card_congr e.toEquiv).symm.trans (hLb i).2).trans (pow_one 3).symm
    exact IsPGroup.of_card hcard
  have hBsub : ∀ i, (imageOTwoQuot Y (Lb i)).IsSubnormal := fun i =>
    (hLb i).1.2.2.map (QuotientGroup.mk'_surjective _)
  have hBQ : ∀ i, imageOTwoQuot Y (Lb i) ≤ pCoreOf 3 (⊤ : Subgroup (OTwoQuot Y)) := by
    intro i
    have hsub : IsSubnormal (imageOTwoQuot Y (Lb i)) ⊤ := A3.subnormal_top_iff.mpr (hBsub i)
    have h1 : imageOTwoQuot Y (Lb i) ≤ pCoreOf 3 (imageOTwoQuot Y (Lb i)) :=
      le_pCoreOf_of_le_normalizer 3 le_rfl Subgroup.le_normalizer (hB3 i)
    exact h1.trans (A4.pCoreOf_le_of_subnormal 3 hsub)
  have hQn : (pCoreOf 3 (⊤ : Subgroup (OTwoQuot Y))).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_pCoreOf 3 ⊤))
  have hx : ∀ x ∈ imageOTwoQuot Y L, ∃ m ∈ imageOTwoQuot Y (M₁ ⊓ Y),
      ∃ b : Fin r → OTwoQuot Y, (∀ i, b i ∈ imageOTwoQuot Y (Lb i)) ∧
        x = m * (List.ofFn b).prod := by
    intro x hx
    obtain ⟨l, hl, hlL, rfl⟩ := mem_imageOTwoQuot_iff.mp hx
    obtain ⟨m, hm, xs, hxs, hlm⟩ := hprod l (hLY hlL)
    have hxsY : ∀ i, xs i ∈ Y := fun i => (hLb i).1.2.1 (hxs i)
    refine ⟨QuotientGroup.mk ⟨m, hm.2⟩, mem_imageOTwoQuot_iff.mpr ⟨m, hm.2, hm, rfl⟩,
      fun i => QuotientGroup.mk ⟨xs i, hxsY i⟩,
      fun i => mem_imageOTwoQuot_iff.mpr ⟨xs i, hxsY i, hxs i, rfl⟩, ?_⟩
    have h1 : (⟨l, hl⟩ : ↥Y) =
        ⟨m, hm.2⟩ * (List.ofFn fun i => (⟨xs i, hxsY i⟩ : ↥Y)).prod := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, SubmonoidClass.coe_list_prod, List.map_ofFn]
      exact hlm
    rw [h1, QuotientGroup.mk_mul]
    congr 1
    have := map_list_prod (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Y))
      (List.ofFn fun i => (⟨xs i, hxsY i⟩ : ↥Y))
    rw [List.map_ofFn] at this
    exact this
  have hle := le_of_forall_eq_mul_prod_of_commute hKperf (pCoreOf_isPGroup 3 (⊤ : Subgroup (OTwoQuot Y)))
    (fun i => imageOTwoQuot Y (Lb i)) hBQ
    (fun i => commute_of_perfect_normal hKperf (pCoreOf_isPGroup 3 (⊤ : Subgroup (OTwoQuot Y)))
      (hBQ i) hTC) hx
  intro l hl
  have hlY : l ∈ Y := hLY hl
  exact (mem_of_mk_mem_imageOTwoQuot hOY
    (hle (mem_imageOTwoQuot_iff.mpr ⟨l, hlY, hl, rfl⟩) : (QuotientGroup.mk ⟨l, hlY⟩ : OTwoQuot Y) ∈
      imageOTwoQuot Y (M₁ ⊓ Y))).1

end Assembly

end CFSG.Quasithin.He10
