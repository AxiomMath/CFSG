module

public import CFSG.RankThree.PartTwo.Sec15.SimsBaumannCases
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3
import CFSG.RankThree.PartTwo.Sec19.Item194Proof
import CFSG.RankThree.PartTwo.Sec15.Item153PushProofTools
import CFSG.GH74.GLS.IVK.Proofs2.NatModGrp
import CFSG.RankThree.PartTwo.KFacts.KS116ProofTools
import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.RankThree.PartTwo.Sec15.SimsBaumann

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.GH74.GLS
open CFSG.GH74.GLS.IVK.Proofs2 (SL2 upperSL lowerSL Qup Bor)

variable {X : Type} [Group X]

section SL

variable {F : Type} [Field F]

private def sbl2_sl (a b c d : F) (h : a * d - b * c = 1) : SL2 F :=
  ⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact h⟩

private theorem sbl2_coe_sl (a b c d : F) (h : a * d - b * c = 1) :
    (sbl2_sl a b c d h : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] := rfl

private theorem sbl2_lowerSL_mem {Y : Subgroup (SL2 F)}
    (hU : ∀ t : F, upperSL t ∈ Y) {a b c d : F} (hdet : a * d - b * c = 1)
    (hc : c ≠ 0) (hy : sbl2_sl a b c d hdet ∈ Y) : ∀ z : F, lowerSL z ∈ Y := by
  have hb : b = (a * d - 1) / c := by
    field_simp
    linear_combination (-1 : F) * hdet
  subst hb
  have hwdet : (0 : F) * 0 - (-c⁻¹) * c = 1 := by field_simp; ring
  have hwY : sbl2_sl 0 (-c⁻¹) c 0 hwdet ∈ Y := by
    have h : sbl2_sl 0 (-c⁻¹) c 0 hwdet =
        upperSL (-a / c) * sbl2_sl a ((a * d - 1) / c) c d hdet * upperSL (-d / c) := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.SpecialLinearGroup.coe_mul, IVK.Proofs2.coe_upperSL, sbl2_coe_sl,
          Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
    rw [h]
    exact Y.mul_mem (Y.mul_mem (hU _) hy) (hU _)
  intro z
  have hcomm : lowerSL z * sbl2_sl 0 (-c⁻¹) c 0 hwdet =
      sbl2_sl 0 (-c⁻¹) c 0 hwdet * upperSL (-z / c ^ 2) := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_mul, IVK.Proofs2.coe_upperSL,
        IVK.Proofs2.coe_lowerSL, sbl2_coe_sl, Matrix.mul_apply, Fin.sum_univ_two] <;>
      field_simp
  have h2 : lowerSL z = sbl2_sl 0 (-c⁻¹) c 0 hwdet * upperSL (-z / c ^ 2) *
      (sbl2_sl 0 (-c⁻¹) c 0 hwdet)⁻¹ :=
    eq_mul_inv_of_mul_eq hcomm
  rw [h2]
  exact Y.mul_mem (Y.mul_mem hwY (hU _)) (Y.inv_mem hwY)

private theorem sbl2_eq_top_of_Qup_le {Y : Subgroup (SL2 F)} (hUY : Qup F ≤ Y)
    (hY : ¬ Y ≤ Bor F) : Y = ⊤ := by
  have hU : ∀ t : F, upperSL t ∈ Y := fun t => hUY (IVK.Proofs2.upperSL_mem_Qup t)
  have hL : ∀ t : F, lowerSL t ∈ Y := by
    obtain ⟨y, hyY, hyB⟩ := IsConcreteLE.not_le_iff_exists.mp hY
    revert hyY hyB
    refine Matrix.SpecialLinearGroup.fin_two_induction
      (fun y => y ∈ Y → y ∉ Bor F → ∀ z : F, lowerSL z ∈ Y) ?_ y
    intro a b c d hdet hyY hyB
    have hc : c ≠ 0 := fun h => hyB (by
      show (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
      simp [h])
    exact sbl2_lowerSL_mem hU hdet hc hyY
  refine eq_top_iff.2 ?_
  rw [← IVK.Proofs2.Qup_sup_Qlow (F := F)]
  refine sup_le hUY ?_
  intro g hg
  obtain ⟨t, rfl⟩ := IVK.Proofs2.mem_Qlow.1 hg
  exact hL t

private theorem sbl2_sl2_dichotomy [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    {U Y : Subgroup (SL2 F)} (hU : IsPGroup 2 U) (hUi : ¬ 2 ∣ U.index) (hUY : U ≤ Y) :
    Y = ⊤ ∨ Y ≤ Subgroup.normalizer (U : Set (SL2 F)) := by
  have hQ := IVK.Proofs2.isPGroup_and_index_of_card_eq Nat.prime_two hF
    (IVK.Proofs2.card_Qup (F := F))
  have hQs : CFSG.QuasithinUnique.IsSylowTwoOf (Qup F) ⊤ := ⟨le_top, hQ.1, by
    change ¬ 2 ∣ (Qup F).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hQ.2⟩
  have hUs : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ := ⟨le_top, hU, by
    change ¬ 2 ∣ U.relIndex ⊤
    rwa [Subgroup.relIndex_top_right]⟩
  obtain ⟨g, -, hg⟩ := CFSG.Quasithin.B6.isSylowTwoOf_exists_conj hQs hUs
  have hmem : ∀ x, x ∈ U ↔ g⁻¹ * x * g ∈ Qup F := fun x => by
    rw [hg, CFSG.Quasithin.B6.mem_conjSub]
  by_cases hYn : Y ≤ Subgroup.normalizer (U : Set (SL2 F))
  · exact Or.inr hYn
  · left
    obtain ⟨y, hyY, hyn⟩ := IsConcreteLE.not_le_iff_exists.mp hYn
    set Y₀ : Subgroup (SL2 F) := Y.comap (MulAut.conj g).toMonoidHom
    have hmem₀ : ∀ x, x ∈ Y₀ ↔ g * x * g⁻¹ ∈ Y := fun x => Iff.rfl
    have hQY₀ : Qup F ≤ Y₀ := by
      intro q hq
      rw [hmem₀]
      refine hUY ((hmem _).2 ?_)
      have e1 : g⁻¹ * (g * q * g⁻¹) * g = q := by group
      rw [e1]
      exact hq
    have hy₀ : g⁻¹ * y * g ∉ Bor F := by
      intro hb
      apply hyn
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have h1 := Subgroup.mem_normalizer_iff.mp (IVK.Proofs2.Bor_le_normalizer hb) (g⁻¹ * h * g)
      have e1 : g⁻¹ * y * g * (g⁻¹ * h * g) * (g⁻¹ * y * g)⁻¹ = g⁻¹ * (y * h * y⁻¹) * g := by
        group
      rw [e1] at h1
      rw [hmem h, hmem (y * h * y⁻¹)]
      exact h1
    have hy₀Y : g⁻¹ * y * g ∈ Y₀ := by
      rw [hmem₀]
      have e1 : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
      rw [e1]
      exact hyY
    have hY₀top : Y₀ = ⊤ := sbl2_eq_top_of_Qup_le hQY₀ fun h => hy₀ (h hy₀Y)
    refine eq_top_iff.2 fun x _ => ?_
    have hx : g⁻¹ * x * g ∈ Y₀ := hY₀top ▸ Subgroup.mem_top _
    rw [hmem₀] at hx
    have e1 : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [e1] at hx

private theorem sbl2_dichotomy {G : Type} [Group G] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    {Lb : Subgroup G} (e : ↥Lb ≃* SL2 F) {U Y : Subgroup G}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U Lb) (hUY : U ≤ Y) (hYL : Y ≤ Lb) :
    Y = Lb ∨ Y ≤ Subgroup.normalizer (U : Set G) := by
  set U₁ : Subgroup (SL2 F) := (U.subgroupOf Lb).map e.toMonoidHom with hU₁
  set Y₁ : Subgroup (SL2 F) := (Y.subgroupOf Lb).map e.toMonoidHom
  have hU₁2 : IsPGroup 2 U₁ :=
    (hU.2.1.comap_of_injective Lb.subtype Lb.subtype_injective).map _
  have hU₁i : ¬ 2 ∣ U₁.index := by
    rw [hU₁]
    exact (Subgroup.index_map_equiv (U.subgroupOf Lb) e).symm ▸ hU.2.2
  have hUY₁ : U₁ ≤ Y₁ := Subgroup.map_mono (Subgroup.comap_mono hUY)
  have hmemU : ∀ v : ↥Lb, e v ∈ U₁ ↔ v ∈ U.subgroupOf Lb := fun v => by
    constructor
    · rintro ⟨u', hu', hu'e⟩
      exact e.injective hu'e ▸ hu'
    · intro hv
      exact ⟨v, hv, rfl⟩
  rcases sbl2_sl2_dichotomy hF hU₁2 hU₁i hUY₁ with h | h
  · left
    have h' : Y.subgroupOf Lb = ⊤ := by
      refine eq_top_iff.2 fun x _ => ?_
      have hx : e x ∈ Y₁ := h ▸ Subgroup.mem_top _
      obtain ⟨x', hx', hxx'⟩ := hx
      exact e.injective hxx' ▸ hx'
    exact le_antisymm hYL (Subgroup.subgroupOf_eq_top.1 h')
  · right
    intro y hy
    have hyL : y ∈ Lb := hYL hy
    have hy₁ : e ⟨y, hyL⟩ ∈ Y₁ := ⟨⟨y, hyL⟩, hy, rfl⟩
    have hn := Subgroup.mem_normalizer_iff.mp (h hy₁)
    have hyn : (⟨y, hyL⟩ : ↥Lb) ∈
        Subgroup.normalizer ((U.subgroupOf Lb : Subgroup ↥Lb) : Set ↥Lb) := by
      rw [Subgroup.mem_normalizer_iff]
      intro u
      have h2 := hn (e u)
      have e2 : e ⟨y, hyL⟩ * e u * (e ⟨y, hyL⟩)⁻¹ = e (⟨y, hyL⟩ * u * ⟨y, hyL⟩⁻¹) := by simp
      rw [e2, hmemU, hmemU] at h2
      exact h2
    have hyn' : (⟨y, hyL⟩ : ↥Lb) ∈ (Subgroup.normalizer (U : Set G)).subgroupOf Lb := by
      rw [Subgroup.subgroupOf_normalizer_eq hU.1]
      exact hyn
    exact Subgroup.mem_subgroupOf.mp hyn'

private theorem sbl2_sl2_nonabelian : ∃ a b : SL2 F, a * b ≠ b * a := by
  refine ⟨upperSL 1, lowerSL 1, fun h => ?_⟩
  have h1 := congrArg (fun g : SL2 F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp [Matrix.SpecialLinearGroup.coe_mul, IVK.Proofs2.coe_upperSL, IVK.Proofs2.coe_lowerSL,
    Matrix.mul_apply, Fin.sum_univ_two] at h1

private theorem sbl2_sl2_isSimple [CharP F 2] (h4 : 4 ≤ Nat.card F) : IsSimpleGroup (SL2 F) := by
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  exact (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := F)).symm.isSimpleGroup

private theorem sbl2_sylow_ne_bot {G : Type} [Group G] [Finite F] {n : ℕ} (hn : n ≠ 0)
    (hF : Nat.card F = 2 ^ n) {Lb : Subgroup G} (e : ↥Lb ≃* SL2 F) {U : Subgroup G}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U Lb) : U ≠ ⊥ := by
  intro hbot
  have h1 : U.subgroupOf Lb = ⊥ := by
    rw [hbot]
    ext x
    simp
  have h2 := hU.2.2
  rw [h1, Subgroup.index_bot, Nat.card_congr e.toEquiv,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF] at h2
  exact h2 (Dvd.dvd.mul_right (dvd_pow_self 2 hn) _)

private theorem sbl2_not_le_normalizer {G : Type} [Group G] [Finite G] [Finite F] [CharP F 2]
    {n : ℕ}
    (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) {Lb : Subgroup G} (e : ↥Lb ≃* SL2 F)
    {U : Subgroup G} (hU : CFSG.QuasithinUnique.IsSylowTwoOf U Lb) :
    ¬ Lb ≤ Subgroup.normalizer (U : Set G) := by
  intro hN
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  haveI : IsSimpleGroup (SL2 F) := sbl2_sl2_isSimple h4
  haveI : IsSimpleGroup ↥Lb := e.isSimpleGroup
  haveI hnorm : (U.subgroupOf Lb).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hU.1).2 hN
  rcases hnorm.eq_bot_or_eq_top with h | h
  · refine sbl2_sylow_ne_bot (by omega) hF e hU (eq_bot_iff.2 fun u hu => ?_)
    have hul : u ∈ Lb := hU.1 hu
    have hmem : (⟨u, hul⟩ : ↥Lb) ∈ (⊥ : Subgroup ↥Lb) := by
      rw [← h]
      exact hu
    exact Subgroup.mem_bot.2 (congrArg Subtype.val (Subgroup.mem_bot.1 hmem))
  · have hLU : Lb ≤ U := Subgroup.subgroupOf_eq_top.1 h
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 ↥Lb := hU.2.1.to_le hLU
    haveI := hp.isNilpotent
    obtain ⟨a, b, hab⟩ := sbl2_sl2_nonabelian (F := F)
    refine hab ?_
    have := IsSimpleGroup.comm_iff_isSolvable.2 (inferInstance : Group.IsSolvable ↥Lb)
      (e.symm a) (e.symm b)
    simpa using congrArg e this

private theorem sbl2_key {G : Type} [Group G] [Finite G] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n)
    {Lb : Subgroup G} (hLb : Lb.Normal) (e : ↥Lb ≃* SL2 F) {U K : Subgroup G}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U Lb) (hUK : U ≤ K) :
    Lb ≤ K ∨ K ≤ Subgroup.normalizer (U : Set G) := by
  have hUY : U ≤ K ⊓ Lb := le_inf hUK hU.1
  rcases sbl2_dichotomy hF e hU hUY inf_le_right with h | h
  · exact Or.inl (inf_eq_right.1 h)
  · right
    intro k hk
    have hkL : k ∈ Subgroup.normalizer (Lb : Set G) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hLb]
      exact Subgroup.mem_top k
    have hU' : CFSG.QuasithinUnique.IsSylowTwoOf (CFSG.Quasithin.B6.conjSub k U) Lb := by
      have := CFSG.Quasithin.B6.isSylowTwoOf_conjSub hU k
      rwa [CFSG.Quasithin.B6.conjSub_eq_self hkL] at this
    have hU'Y : CFSG.Quasithin.B6.conjSub k U ≤ K ⊓ Lb := by
      refine le_inf (fun x hx => ?_) hU'.1
      rw [CFSG.Quasithin.B6.mem_conjSub] at hx
      have e1 : x = k * (k⁻¹ * x * k) * k⁻¹ := by group
      rw [e1]
      exact K.mul_mem (K.mul_mem hk (hUK hx)) (K.inv_mem hk)
    obtain ⟨g, hg, hgU⟩ := CFSG.Quasithin.B6.isSylowTwoOf_exists_conj
      (CFSG.Quasithin.B6.isSylowTwoOf_mono hU hUY inf_le_right)
      (CFSG.Quasithin.B6.isSylowTwoOf_mono hU' hU'Y inf_le_right)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hgU.trans (CFSG.Quasithin.B6.conjSub_eq_self (h hg))

end SL

private instance sbl2_normal_oResidual (Y : Type) [Group Y] : (oResidual 2 Y).Normal := by
  refine ⟨fun n hn g => ?_⟩
  unfold oResidual at hn ⊢
  have key : Subgroup.map (MulAut.conj g).toMonoidHom
      (Subgroup.closure {x : Y | Nat.Coprime (orderOf x) 2}) ≤
      Subgroup.closure {x : Y | Nat.Coprime (orderOf x) 2} := by
    rw [MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨x, hx, rfl⟩
    show Nat.Coprime (orderOf (MulAut.conj g x)) 2
    rwa [MulEquiv.orderOf_eq]
  exact key ⟨n, hn, rfl⟩

private theorem sbl2_exists_pow_mem_oResidual {Y : Type} [Group Y] [Finite Y] (x : Y) :
    ∃ k : ℕ, x ^ 2 ^ k ∈ oResidual 2 Y := by
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  refine ⟨k, Subgroup.subset_closure ?_⟩
  show Nat.Coprime (orderOf (x ^ 2 ^ k)) 2
  rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨m, hn⟩, hn,
    Nat.mul_div_cancel_left _ (by positivity)]
  exact hm.coprime_two_right

private theorem sbl2_normalizer_le_of_char {S C : Subgroup X} (hCS : C ≤ S)
    (hC : (C.subgroupOf S).Characteristic) :
    Subgroup.normalizer (S : Set X) ≤ Subgroup.normalizer (C : Set X) := by
  have key : ∀ g ∈ Subgroup.normalizer (S : Set X), ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
    intro g hg c hc
    have hg' : g⁻¹ ∈ Subgroup.normalizer (S : Set X) := inv_mem hg
    let φ : ↥S ≃* ↥S :=
      { toFun := fun s => ⟨g * s * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg s).mp s.2⟩
        invFun := fun s => ⟨g⁻¹ * s * g, by
          have := (Subgroup.mem_normalizer_iff.mp hg' s).mp s.2
          simpa using this⟩
        left_inv := fun s => by ext; simp [mul_assoc]
        right_inv := fun s => by ext; simp [mul_assoc]
        map_mul' := fun a b => by ext; simp [mul_assoc] }
    have hcS : (⟨c, hCS hc⟩ : ↥S) ∈ C.subgroupOf S := hc
    exact Subgroup.characteristic_iff_le_comap.mp hC φ hcS
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

private noncomputable def sbl2_equivSL {n : ℕ}
    (e : ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 n)) :
    ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) ≃* SL2 (GaloisField 2 n) :=
  e.trans (CFSG.RankThree.PartTwo.KFacts.KS116Proof.projSLEquiv (GaloisField 2 n)).symm

private theorem sbl2_isSimple {n : ℕ} (hn : 2 ≤ n)
    (e : ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 n)) :
    IsSimpleGroup ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) := by
  have h4 : 4 ≤ Nat.card (GaloisField 2 n) := by
    rw [GaloisField.card 2 n (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  haveI : IsSimpleGroup (SL2 (GaloisField 2 n)) := sbl2_sl2_isSimple h4
  exact (sbl2_equivSL e).isSimpleGroup

private theorem sbl2_odd_mem_of_isSubnormal {Q : Subgroup X} [Q.Normal] (hQ : IsPGroup 2 Q)
    {H K : Subgroup X} (hHK : CFSG.Open.IsSubnormal H K) (hKQ : K ≤ H ⊔ Q) {x : X}
    (hx : x ∈ K) (hodd : Nat.Coprime (orderOf x) 2) : x ∈ H := by
  induction hHK with
  | refl H => exact hx
  | @step H M K hHM hN _ ih =>
    have hMQ : K ≤ M ⊔ Q := hKQ.trans (sup_le_sup_right hHM Q)
    have hxM : x ∈ M := ih hMQ hx
    have hMn : M ≤ Subgroup.normalizer (H : Set X) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).1 hN
    obtain ⟨h, hh, q, hq, hxq⟩ := Subgroup.mem_sup_of_normal_right.1 (hKQ hx)
    have hqM : q ∈ M := by
      have : q = h⁻¹ * x := by rw [← hxq]; group
      rw [this]
      exact M.mul_mem (M.inv_mem (hHM hh)) hxM
    have hxs : x ∈ H ⊔ (M ⊓ Q) := by
      rw [← hxq]
      exact Subgroup.mul_mem_sup hh ⟨hqM, hq⟩
    obtain ⟨a, ha⟩ := Push153.exists_pow_two_mem_of_sup (hQ.to_le inf_le_right)
      (inf_le_left.trans hMn) hxs
    have hcop : Nat.Coprime (2 ^ a) (orderOf x) := (Nat.Coprime.pow_left a hodd.symm)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm]
    exact H.pow_mem ha m

private theorem sbl2_oResidual_le {Y : Subgroup X}
    (h : ∀ x : X, Nat.Coprime (orderOf x) 2 → x ∈ Y) : oResidual 2 X ≤ Y :=
  (Subgroup.closure_le Y).2 fun x hx => h x hx

variable [Finite X]

private theorem sbl2_oResidual_quot :
    oResidual 2 (X ⧸ CFSG.pCore 2 X) =
      (oResidual 2 X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) := by
  refine Push153.oResidual_eq_of_pow (Push153.map_oResidual_le _) fun y => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 X) y
  obtain ⟨a, ha⟩ := sbl2_exists_pow_mem_oResidual x
  exact ⟨a, by rw [← map_pow]; exact ⟨_, ha, rfl⟩⟩

private theorem sbl2_isSylow_image {S : Subgroup X} (hQS : CFSG.pCore 2 X ≤ S)
    (hS2 : IsPGroup 2 S)
    (hsyl : CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ (oResidual 2 X ⊔ CFSG.pCore 2 X))
      (oResidual 2 X ⊔ CFSG.pCore 2 X)) :
    CFSG.QuasithinUnique.IsSylowTwoOf
      ((S ⊓ (oResidual 2 X ⊔ CFSG.pCore 2 X)).map (QuotientGroup.mk' (CFSG.pCore 2 X)))
      (oResidual 2 (X ⧸ CFSG.pCore 2 X)) := by
  set π : X →* X ⧸ CFSG.pCore 2 X := QuotientGroup.mk' (CFSG.pCore 2 X) with hπ
  set M : Subgroup X := oResidual 2 X ⊔ CFSG.pCore 2 X with hM
  have hQM : CFSG.pCore 2 X ≤ M := le_sup_right
  have hQSM : CFSG.pCore 2 X ≤ S ⊓ M := le_inf hQS hQM
  have hMπ : M.map π = oResidual 2 (X ⧸ CFSG.pCore 2 X) := by
    rw [hM, Subgroup.map_sup, sbl2_oResidual_quot, hπ, QuotientGroup.map_mk'_self, sup_bot_eq]
  have hrel : ((S ⊓ M).map π).relIndex (M.map π) = (S ⊓ M).relIndex M := by
    rw [Subgroup.relIndex_map_map, hπ, QuotientGroup.ker_mk', sup_of_le_left hQSM,
      sup_of_le_left hQM]
  rw [hMπ] at hrel
  refine ⟨?_, (hS2.to_le inf_le_left).map π, ?_⟩
  · rw [← hMπ]
    exact Subgroup.map_mono inf_le_right
  · change ¬ 2 ∣ ((S ⊓ M).map π).relIndex (oResidual 2 (X ⧸ CFSG.pCore 2 X))
    rw [hrel]
    exact hsyl.2.2

private theorem sbl2_isSylow_sup {S : Subgroup X} (hS2 : IsPGroup 2 S)
    (hsyl : CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ (oResidual 2 X ⊔ CFSG.pCore 2 X))
      (oResidual 2 X ⊔ CFSG.pCore 2 X)) :
    CFSG.QuasithinUnique.IsSylowTwoOf S (S ⊔ oResidual 2 X ⊔ CFSG.pCore 2 X) := by
  refine ⟨le_sup_left.trans le_sup_left, hS2, ?_⟩
  have hSM : S ≤ Subgroup.normalizer ((oResidual 2 X ⊔ CFSG.pCore 2 X : Subgroup X) : Set X) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  change ¬ 2 ∣ S.relIndex (S ⊔ oResidual 2 X ⊔ CFSG.pCore 2 X)
  rw [sup_assoc, ← CFSG.Quasithin.B6.relIndex_inf_eq_relIndex_sup hSM]
  exact hsyl.2.2

private theorem sbl2_charTwo (hF : generalizedFitting X = CFSG.pCore 2 X) {N : Subgroup X}
    (hQN : CFSG.pCore 2 X ≤ N) : CFSG.QuasithinUnique.CharTwo N := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : IsCharacteristicP 2 X :=
    (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore X 2).mpr hF
  have hQ : CFSG.pCore 2 X ≤ CFSG.Open.pCoreOf 2 N :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQN
      (by rw [Subgroup.normalizer_eq_top_iff.mpr CFSG.pCore_normal]; exact le_top)
      CFSG.pCore_isPGroup
  rintro x ⟨-, hxC⟩
  have hxQ : x ∈ CFSG.pCore 2 X :=
    hchar (Subgroup.centralizer_le (fun q hq => hQ hq) hxC)
  exact hQ hxQ

private theorem sbl2_cgsIn_ne {S : Subgroup X} {n : ℕ} (hn : 2 ≤ n)
    (e : ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 n))
    (hQS : CFSG.pCore 2 X ≤ S) (hS2 : IsPGroup 2 S)
    (hsyl : CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ (oResidual 2 X ⊔ CFSG.pCore 2 X))
      (oResidual 2 X ⊔ CFSG.pCore 2 X))
    (hnorm : (S ⊔ oResidual 2 X ⊔ CFSG.pCore 2 X).Normal)
    (hno : ¬ ∃ C : Subgroup X, C ≠ ⊥ ∧ C ≤ S ∧ (C.subgroupOf S).Characteristic ∧ C.Normal) :
    CFSG.Quasithin.cgsIn (S ⊔ oResidual 2 X ⊔ CFSG.pCore 2 X) S ≠
      S ⊔ oResidual 2 X ⊔ CFSG.pCore 2 X := by
  classical
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have hLb := sbl2_oResidual_quot (X := X)
  have hUsyl := sbl2_isSylow_image hQS hS2 hsyl
  have hSyl := sbl2_isSylow_sup hS2 hsyl
  haveI := hnorm
  set P : Subgroup X := (Subgroup.normalizer
    (((S ⊓ (oResidual 2 X ⊔ CFSG.pCore 2 X)).map (QuotientGroup.mk' (CFSG.pCore 2 X)) :
      Subgroup (X ⧸ CFSG.pCore 2 X)) : Set (X ⧸ CFSG.pCore 2 X))).comap
    (QuotientGroup.mk' (CFSG.pCore 2 X))
  have hle : CFSG.Quasithin.cgsIn (S ⊔ oResidual 2 X ⊔ CFSG.pCore 2 X) S ≤ P := by
    refine iSup_le fun C => iSup_le fun hCS => iSup_le fun hC0 => iSup_le fun hCc => ?_
    have hSN : S ≤ Subgroup.normalizer (C : Set X) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hCS).1 inferInstance
    have hSK : S ≤ (S ⊔ oResidual 2 X ⊔ CFSG.pCore 2 X) ⊓ Subgroup.normalizer (C : Set X) :=
      le_inf (le_sup_left.trans le_sup_left) hSN
    have hUK : (S ⊓ (oResidual 2 X ⊔ CFSG.pCore 2 X)).map (QuotientGroup.mk' (CFSG.pCore 2 X)) ≤
        ((S ⊔ oResidual 2 X ⊔ CFSG.pCore 2 X) ⊓ Subgroup.normalizer (C : Set X)).map
          (QuotientGroup.mk' (CFSG.pCore 2 X)) :=
      Subgroup.map_mono (inf_le_left.trans hSK)
    rcases sbl2_key hF inferInstance (sbl2_equivSL e) hUsyl hUK with h | h
    · exfalso
      have hLK : oResidual 2 X ≤ (S ⊔ oResidual 2 X ⊔ CFSG.pCore 2 X) ⊓
          Subgroup.normalizer (C : Set X) := by
        intro l hl
        have hπl : QuotientGroup.mk' (CFSG.pCore 2 X) l ∈ ((S ⊔ oResidual 2 X ⊔
            CFSG.pCore 2 X) ⊓ Subgroup.normalizer (C : Set X)).map
            (QuotientGroup.mk' (CFSG.pCore 2 X)) :=
          h (by rw [hLb]; exact Subgroup.mem_map_of_mem _ hl)
        obtain ⟨k, hk, hkl⟩ := hπl
        have hkq : k⁻¹ * l ∈ CFSG.pCore 2 X := QuotientGroup.eq.1 hkl
        have e1 : l = k * (k⁻¹ * l) := by group
        rw [e1]
        exact Subgroup.mul_mem _ hk (hSK (hQS hkq))
      have hX₀N : S ⊔ oResidual 2 X ⊔ CFSG.pCore 2 X ≤ Subgroup.normalizer (C : Set X) :=
        sup_le (sup_le hSN (hLK.trans inf_le_right)) (hQS.trans hSN)
      have hfr := CFSG.Quasithin.B6.frattini_two
        (le_top : S ⊔ oResidual 2 X ⊔ CFSG.pCore 2 X ≤ ⊤)
        (Subgroup.normalizer_eq_top_iff.mpr hnorm).ge hSyl
      have htop : (⊤ : Subgroup X) ≤ Subgroup.normalizer (C : Set X) :=
        hfr.trans (sup_le hX₀N (inf_le_right.trans (sbl2_normalizer_le_of_char hCS hCc)))
      exact hno ⟨C, hC0, hCS, hCc, Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp htop)⟩
    · intro k hk
      exact h (Subgroup.mem_map_of_mem _ hk)
  intro heq
  have hXP : S ⊔ oResidual 2 X ⊔ CFSG.pCore 2 X ≤ P := heq.ge.trans hle
  refine sbl2_not_le_normalizer hn hF (sbl2_equivSL e) hUsyl ?_
  rw [hLb]
  rintro _ ⟨l, hl, rfl⟩
  exact hXP (Subgroup.mem_sup_left (Subgroup.mem_sup_right hl))

private theorem sbl2_eq_oResidual {S : Subgroup X} {n : ℕ} (hn : 2 ≤ n)
    (e : ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 n))
    (hQS : CFSG.pCore 2 X ≤ S) (hS2 : IsPGroup 2 S)
    (hsyl : CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ (oResidual 2 X ⊔ CFSG.pCore 2 X))
      (oResidual 2 X ⊔ CFSG.pCore 2 X))
    {Y : Subgroup X} (hYX₀ : Y ≤ S ⊔ oResidual 2 X ⊔ CFSG.pCore 2 X)
    (hYsub : CFSG.Open.IsSubnormal Y (S ⊔ oResidual 2 X ⊔ CFSG.pCore 2 X))
    (hYshort : CFSG.QuasithinUnique.IsShort2 Y)
    (hYnle : ¬ Y ≤ CFSG.Quasithin.cgsIn (S ⊔ oResidual 2 X ⊔ CFSG.pCore 2 X) S) :
    Y = oResidual 2 X := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have hker : (QuotientGroup.mk' (CFSG.pCore 2 X)).ker = CFSG.pCore 2 X :=
    QuotientGroup.ker_mk' (N := CFSG.pCore 2 X)
  have hLb := sbl2_oResidual_quot (X := X)
  have hsimple := sbl2_isSimple hn e
  have hUsyl := sbl2_isSylow_image hQS hS2 hsyl
  have hLX₀ : oResidual 2 X ≤ S ⊔ oResidual 2 X ⊔ CFSG.pCore 2 X := le_sup_right.trans le_sup_left
  have hMX₀ : oResidual 2 X ⊔ CFSG.pCore 2 X ≤ S ⊔ oResidual 2 X ⊔ CFSG.pCore 2 X :=
    sup_le hLX₀ le_sup_right
  have hYL : Y ≤ oResidual 2 X := by
    haveI : ((oResidual 2 X).subgroupOf Y).Normal := inferInstance
    have hP : IsPGroup 2 (↥Y ⧸ (oResidual 2 X).subgroupOf Y) := by
      intro g
      induction g using QuotientGroup.induction_on with
      | H y =>
        obtain ⟨k, hk⟩ := sbl2_exists_pow_mem_oResidual (y : X)
        refine ⟨k, ?_⟩
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        simpa using hk
    have htop := hYshort.1 ((oResidual 2 X).subgroupOf Y) hP
    intro y hy
    have : (⟨y, hy⟩ : ↥Y) ∈ (oResidual 2 X).subgroupOf Y := htop ▸ Subgroup.mem_top _
    exact this
  have hYb : Y.map (QuotientGroup.mk' (CFSG.pCore 2 X)) ≤ oResidual 2 (X ⧸ CFSG.pCore 2 X) := by
    rw [hLb]
    exact Subgroup.map_mono hYL
  have hsub : CFSG.Open.IsSubnormal (Y.map (QuotientGroup.mk' (CFSG.pCore 2 X)))
      (oResidual 2 (X ⧸ CFSG.pCore 2 X)) := by
    have hLbX : oResidual 2 (X ⧸ CFSG.pCore 2 X) ≤
        (S ⊔ oResidual 2 X ⊔ CFSG.pCore 2 X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) := by
      rw [hLb]
      exact Subgroup.map_mono hLX₀
    have h1 := (hYsub.map (QuotientGroup.mk' (CFSG.pCore 2 X))).inf_of_le hLbX
    rwa [inf_eq_left.2 hYb] at h1
  rcases hsub.eq_bot_or_eq_of_isSimpleGroup hsimple with h | h
  · exfalso
    have hYQ : Y ≤ CFSG.pCore 2 X := by
      rw [← hker]
      exact (Subgroup.map_eq_bot_iff _).1 h
    have hS0 : S ≠ ⊥ := by
      intro hS0
      refine sbl2_sylow_ne_bot (by omega) hF (sbl2_equivSL e) hUsyl ?_
      rw [hS0, bot_inf_eq, Subgroup.map_bot]
    exact hYnle ((le_inf hYX₀ ((hYQ.trans hQS).trans Subgroup.le_normalizer)).trans
      (CFSG.Quasithin.inf_normalizer_le_cgsIn hS0))
  · have hsup : Y ⊔ CFSG.pCore 2 X = oResidual 2 X ⊔ CFSG.pCore 2 X := by
      have h1 := Subgroup.comap_map_eq (QuotientGroup.mk' (CFSG.pCore 2 X)) Y
      have h2 := Subgroup.comap_map_eq (QuotientGroup.mk' (CFSG.pCore 2 X)) (oResidual 2 X)
      rw [hker] at h1 h2
      rw [← h1, ← h2, h, hLb]
    have hYM : CFSG.Open.IsSubnormal Y (oResidual 2 X ⊔ CFSG.pCore 2 X) := by
      have h1 := hYsub.inf_of_le hMX₀
      rwa [inf_eq_left.2 (hYL.trans le_sup_left)] at h1
    refine le_antisymm hYL (sbl2_oResidual_le fun x hx => ?_)
    exact sbl2_odd_mem_of_isSubnormal CFSG.pCore_isPGroup hYM hsup.ge
      (Subgroup.mem_sup_left (Subgroup.subset_closure hx)) hx

theorem concl315_of_typeL2_sylow
    (hF : generalizedFitting X = CFSG.pCore 2 X)
    {A S : Subgroup X} (hS : S ∈ maxInvariantPiSubgroups ⊤ A (piOf 2)) {n : ℕ} (hn : 2 ≤ n)
    (e : ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 n))
    (hsyl : CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ (oResidual 2 X ⊔ CFSG.pCore 2 X))
      (oResidual 2 X ⊔ CFSG.pCore 2 X))
    (hKG : CFSG.Open.IsKGroup X)
    (hnorm : (S ⊔ oResidual 2 X ⊔ CFSG.pCore 2 X).Normal) : Concl315 X S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQS : CFSG.pCore 2 X ≤ S := Push153.pCore_le_of_mem_maxInvariant hS
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp hS.prop.2.1
  by_cases hC : ∃ C : Subgroup X, C ≠ ⊥ ∧ C ≤ S ∧ (C.subgroupOf S).Characteristic ∧ C.Normal
  · exact Or.inl hC
  refine Or.inr ?_
  obtain ⟨Y, hYX₀, hYsub, hYX, hYnle⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalCGTBlock_proved X
      (S ⊔ oResidual 2 X ⊔ CFSG.pCore 2 X) S (hKG.subgroup _)
      (sbl2_charTwo hF (hQS.trans (le_sup_left.trans le_sup_left)))
      (sbl2_isSylow_sup hS2 hsyl) (sbl2_cgsIn_ne hn e hQS hS2 hsyl hnorm hC)
  have hY : Y = oResidual 2 X :=
    sbl2_eq_oResidual hn e hQS hS2 hsyl hYX₀ hYsub hYX.1 hYnle
  subst hY
  exact Sec19.Item194Proof.isScriptLBlock_of_inClassXBlock le_top
    (CFSG.Open.IsSubnormal.of_mathlib (sbl2_normal_oResidual X).isSubnormal) hYX

end CFSG.RankThree.PartTwo.Sec15.SimsBaumann
