module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem2
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative Matrix

namespace Sec121Swap

section InvTranspose

variable {n : ℕ} {R : Type*} [CommRing R]

theorem transpose_mul_sl (A B : Matrix.SpecialLinearGroup (Fin n) R) :
    (A * B).transpose = B.transpose * A.transpose :=
  Subtype.ext (Matrix.transpose_mul _ _)

theorem transpose_transpose_sl (A : Matrix.SpecialLinearGroup (Fin n) R) :
    A.transpose.transpose = A :=
  Subtype.ext (Matrix.transpose_transpose _)

theorem transpose_inv_sl (A : Matrix.SpecialLinearGroup (Fin n) R) :
    (A⁻¹).transpose = (A.transpose)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← transpose_mul_sl, mul_inv_cancel]
  exact Subtype.ext Matrix.transpose_one

theorem exists_mulAut_ne_conj {n : ℕ} (hn : 3 ≤ n) :
    ∃ φ : MulAut (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)), ∀ g, φ ≠ MulAut.conj g := by
  classical
  refine ⟨{ toFun := fun A => (A.transpose)⁻¹
            invFun := fun A => (A.transpose)⁻¹
            left_inv := fun A => by simp only [transpose_inv_sl, transpose_transpose_sl, inv_inv]
            right_inv := fun A => by simp only [transpose_inv_sl, transpose_transpose_sl, inv_inv]
            map_mul' := fun A B => by simp only [transpose_mul_sl, mul_inv_rev] }, fun g h => ?_⟩
  set i₀ : Fin n := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin n := ⟨1, by omega⟩ with hi₁
  set i₂ : Fin n := ⟨2, by omega⟩ with hi₂
  set e₀ : Fin n → ZMod 2 := Pi.single i₀ 1 with he₀
  set v : Fin n → ZMod 2 := (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ e₀ with hv
  have hfix : ∀ i j : Fin n, i ≠ i₀ → i ≠ j → v j = 0 := by
    intro i j hi hij
    set A : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) :=
      ⟨Matrix.transvection j i 1, Matrix.det_transvection_of_ne _ _ hij.symm 1⟩ with hA
    have he₀i : e₀ i = 0 := by simp [he₀, hi]
    have hAe : (A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ e₀ = e₀ := by
      show Matrix.transvection j i 1 *ᵥ e₀ = e₀
      rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec,
        he₀i, mul_zero]
      ext k
      simp
    have hAinv : ((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ e₀ = e₀ := by
      conv_lhs => rw [← hAe]
      rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    have h1 : (A.transpose)⁻¹ = g * A * g⁻¹ := by
      have := congrArg (fun ψ : MulAut (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) => ψ A) h
      simpa [MulAut.conj_apply] using this
    have h2 : A.transpose * g = g * A⁻¹ := by
      rw [← inv_inv A.transpose, h1]
      group
    have h3 : (A.transpose : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v = v := by
      calc (A.transpose : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v =
            ((A.transpose * g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
              Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ e₀ := by
            rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
        _ = ((g * A⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
              Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ e₀ := by rw [h2]
        _ = v := by rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hAinv]
    have hT : (A.transpose : Matrix (Fin n) (Fin n) (ZMod 2)) = Matrix.transvection i j 1 := by
      rw [Matrix.SpecialLinearGroup.coe_transpose]
      show (Matrix.transvection j i (1 : ZMod 2))ᵀ = _
      rw [Matrix.transvection, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single]
      rfl
    rw [hT] at h3
    have h5 := congrFun h3 i
    rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec] at h5
    simpa using h5
  have hv0 : v = 0 := by
    funext j
    by_cases hj : j = i₁
    · exact hfix i₂ j (by simp [hi₂, hi₀, Fin.ext_iff]) (by simp [hj, hi₂, hi₁, Fin.ext_iff])
    · exact hfix i₁ j (by simp [hi₁, hi₀, Fin.ext_iff]) (fun h => hj h.symm)
  have he₀0 : e₀ = 0 := by
    have := congrArg (fun w => ((g⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ w) hv0
    simp only [hv, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, Matrix.mulVec_zero] at this
    exact this
  have := congrFun he₀0 i₀
  simp [he₀] at this

end InvTranspose

section Hyp

variable {G : Type} [Group G] [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ}

omit [Finite G] in
private theorem pCoreOf_subgroupOf_self' (L : Subgroup G) :
    (pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L := CFSG.openPCoreOf_subgroupOf 2 L

theorem mem_normalizer_of_conj_mem {H : Subgroup G} {m : G}
    (h : ∀ a ∈ H, m * a * m⁻¹ ∈ H) : m ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  let f : ↥H → ↥H := fun a => ⟨m * a * m⁻¹, h a a.2⟩
  have hf : Function.Injective f := fun a b hab => by
    have := congrArg Subtype.val hab
    simp only [f, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  obtain ⟨a, ha⟩ := (Finite.injective_iff_surjective.mp hf) ⟨_, hx⟩
  have := congrArg Subtype.val ha
  simp only [f, mul_left_inj, mul_right_inj] at this
  rw [← this]
  exact a.2

theorem swap_of_hyp121 (hyp : Hyp121 G T L V V₁ V₂ n) [IsMulCommutative ↥V] {m : G}
    (hm : m ∈ Subgroup.normalizer (L : Set G)) (hm1 : m ∉ Subgroup.normalizer (V₁ : Set G)) :
    (∀ a ∈ V₁, m * a * m⁻¹ ∈ V₂) ∧ ∀ c ∈ V₂, m * c * m⁻¹ ∈ V₁ := by
  obtain ⟨hcard₁, hcard₂, -⟩ := Sec1212.card_eq_of_hyp121 hyp
  have h1 : ∀ a ∈ V₁, m * a * m⁻¹ ∈ V₂ := by
    rcases Sec1212.conj_mem_of_hyp121 hyp hm with ⟨h, -⟩ | h
    · exact absurd (mem_normalizer_of_conj_mem h) hm1
    · exact h
  have hm1' : m⁻¹ ∉ Subgroup.normalizer (V₁ : Set G) := fun h =>
    hm1 (by simpa using Subgroup.inv_mem _ h)
  have h2 : ∀ a ∈ V₁, m⁻¹ * a * m⁻¹⁻¹ ∈ V₂ := by
    rcases Sec1212.conj_mem_of_hyp121 hyp (Subgroup.inv_mem _ hm) with ⟨h, -⟩ | h
    · exact absurd (mem_normalizer_of_conj_mem h) hm1'
    · exact h
  refine ⟨h1, fun c hc => ?_⟩
  let f : ↥V₁ → ↥V₂ := fun a => ⟨m⁻¹ * a * m⁻¹⁻¹, h2 a a.2⟩
  have hf : Function.Injective f := fun a b hab => by
    have := congrArg Subtype.val hab
    simp only [f, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  have hcard : Nat.card ↥V₂ ≤ Nat.card ↥V₁ := by rw [hcard₁, hcard₂]
  obtain ⟨a, ha⟩ := (hf.bijective_of_nat_card_le hcard).2 ⟨c, hc⟩
  have := congrArg Subtype.val ha
  simp only [f, inv_inv] at this
  rw [← this]
  have e : m * (m⁻¹ * (a : G) * m) * m⁻¹ = a := by group
  rw [e]
  exact a.2

theorem exists_swap_of_hyp121 (hyp : Hyp121 G T L V V₁ V₂ n) [IsMulCommutative ↥V] :
    ∃ m ∈ Subgroup.normalizer (L : Set G), m ∉ Subgroup.normalizer (V₁ : Set G) := by
  by_contra hcon
  have hall : ∀ m ∈ Subgroup.normalizer (L : Set G), m ∈ Subgroup.normalizer (V₁ : Set G) :=
    fun m hm => by_contra fun h => hcon ⟨m, hm, h⟩
  have hn3 : 3 ≤ n := by rcases hyp.rank with h | h <;> omega
  obtain ⟨hc₁, hnat₁⟩ := hyp.nat₁
  have hV₁V : V₁ ≤ V := hyp.sup ▸ le_sup_left
  have hMV := Sec121Q.normalizer_le_of_hyp121 hyp
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := Subgroup.le_normalizer.trans hMV
  have hle : autOn (Subgroup.normalizer (L : Set G)) V ≤ autOn L V := by
    intro y hy
    obtain ⟨⟨m, hm⟩, rfl⟩ := (A4.mem_autOn_iff hMV).mp hy
    have hτ : conjAct V₁ ⟨m, hall m hm⟩ ∈ autOn L V₁ := by
      rw [G64.BinaryNaturalSL.eq_top hnat₁]
      exact Subgroup.mem_top _
    obtain ⟨⟨l, hl⟩, hlτ⟩ := (A4.mem_autOn_iff hyp.norm₁).mp hτ
    have hlm : l⁻¹ * m ∈ Subgroup.centralizer (V : Set G) := by
      refine Sec1212.mem_centralizer_of_hyp121 hyp hV₁V hyp.norm₁ hnat₁
        ((Subgroup.normalizer (L : Set G)).mul_mem
          (Subgroup.inv_mem _ (Subgroup.le_normalizer hl)) hm) ?_
      refine Sec1212.mem_centralizer_iff_conj.mpr fun a ha => ?_
      have h1 := congrArg (fun φ : MulAut ↥V₁ => ((φ ⟨a, ha⟩ : ↥V₁) : G)) hlτ
      simp only [A4.actionOn_apply_coe, InternalSec.coe_conjAct_apply] at h1
      calc l⁻¹ * m * a * (l⁻¹ * m)⁻¹ = l⁻¹ * (m * a * m⁻¹) * l := by group
        _ = l⁻¹ * (l * a * l⁻¹) * l := by rw [h1]
        _ = a := by group
    refine (A4.mem_autOn_iff hLV).mpr ⟨⟨l, hl⟩, MulEquiv.ext fun v => Subtype.ext ?_⟩
    simp only [A4.actionOn_apply_coe]
    have h2 := (Sec1212.mem_centralizer_iff_conj.mp hlm) v v.2
    calc l * (v : G) * l⁻¹ = l * (l⁻¹ * m * v * (l⁻¹ * m)⁻¹) * l⁻¹ := by rw [h2]
      _ = m * v * m⁻¹ := by group
  have hCL : L ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 L :=
    le_antisymm (fun x hx => Sec121Q.inf_centralizer_le_pCoreOf_of_hyp121 hyp hV₁V hyp.norm₁
        hnat₁ ⟨hx.1, Subgroup.centralizer_le (by exact_mod_cast hV₁V) hx.2⟩)
      (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
        (Sec121Q.pCoreOf_le_centralizer_of_hyp121 hyp))
  have hcardL : Nat.card (autOn L V) = Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rw [card_autOn_eq_relIndex hLV, hCL, Subgroup.relIndex, pCoreOf_subgroupOf_self']
    rfl
  obtain ⟨φ⟩ := hyp.aut
  have hfin : Finite (MulAut (↥L ⧸ CFSG.pCore 2 ↥L)) :=
    Finite.of_injective (fun f : MulAut (↥L ⧸ CFSG.pCore 2 ↥L) =>
      (f : (↥L ⧸ CFSG.pCore 2 ↥L) → (↥L ⧸ CFSG.pCore 2 ↥L))) DFunLike.coe_injective
  have hcardM : Nat.card (MulAut (↥L ⧸ CFSG.pCore 2 ↥L)) ≤ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rw [← Nat.card_congr φ.toEquiv, ← hcardL]
    exact Subgroup.card_le_of_le hle
  obtain ⟨eL⟩ := hyp.iso
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
    CFSG.Quasithin.Vol2.Ch11.SecA.isSimpleGroup_SL_zmod_two hn3
  have : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := eL.isSimpleGroup
  obtain ⟨a, b, hab⟩ := Sec121Thm.exists_not_commute_SL hn3
  have hinj : Function.Injective
      (MulAut.conj : (↥L ⧸ CFSG.pCore 2 ↥L) →* MulAut (↥L ⧸ CFSG.pCore 2 ↥L)) := by
    rw [injective_iff_map_eq_one]
    intro s hs1
    have hc : s ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := Subgroup.mem_center_iff.mpr fun x => by
      have := congrArg (fun ψ : MulAut (↥L ⧸ CFSG.pCore 2 ↥L) => ψ x) hs1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc x * s = (s * x * s⁻¹) * s := by rw [this]
        _ = s * x := by group
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
      with h | h
    · rw [h] at hc
      exact Subgroup.mem_bot.mp hc
    · exfalso
      apply hab
      have hcomm := (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top (eL.symm b))) (eL.symm a)
      have := congrArg eL hcomm
      simpa using this
  have hbij := hinj.bijective_of_nat_card_le hcardM
  obtain ⟨σ, hσ⟩ := exists_mulAut_ne_conj hn3
  obtain ⟨s, hs⟩ := hbij.2 ((eL.trans σ).trans eL.symm)
  refine hσ (eL s) (MulEquiv.ext fun A => ?_)
  have h1 := congrArg (fun ψ : MulAut (↥L ⧸ CFSG.pCore 2 ↥L) => eL (ψ (eL.symm A))) hs
  simp only [MulAut.conj_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply, map_mul,
    map_inv] at h1
  rw [MulAut.conj_apply, h1]

theorem exists_mem_not_normalizer (hyp : Hyp121 G T L V V₁ V₂ n) [IsMulCommutative ↥V]
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    ∃ t ∈ T, t ∉ Subgroup.normalizer (V₁ : Set G) := by
  obtain ⟨m₀, hm₀, hm₀1⟩ := exists_swap_of_hyp121 hyp
  by_contra hcon
  have hT1 : ∀ t ∈ T, t ∈ Subgroup.normalizer (V₁ : Set G) :=
    fun t ht => by_contra fun h => hcon ⟨t, ht, h⟩
  set M := Subgroup.normalizer (L : Set G) with hM
  set M₁ := M ⊓ Subgroup.normalizer (V₁ : Set G) with hM₁
  have hidx : (M₁.subgroupOf M).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨m₀, hm₀⟩, fun b => xor_iff_iff_not.mpr ?_⟩
    simp only [hM₁, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.mem_inf]
    have hb := b.2
    constructor
    · rintro ⟨-, h1⟩ ⟨-, h2⟩
      have h3 := (Subgroup.normalizer (V₁ : Set G)).mul_mem (Subgroup.inv_mem _ h2) h1
      exact hm₀1 (by simpa using h3)
    · intro hb1
      have hb1' : (b : G) ∉ Subgroup.normalizer (V₁ : Set G) := fun h => hb1 ⟨hb, h⟩
      refine ⟨M.mul_mem hb hm₀, mem_normalizer_of_conj_mem fun a ha => ?_⟩
      have h1 := (swap_of_hyp121 hyp hm₀ hm₀1).1 a ha
      have h2 := (swap_of_hyp121 hyp hb hb1').2 _ h1
      have e : (b : G) * m₀ * a * ((b : G) * m₀)⁻¹ = b * (m₀ * a * m₀⁻¹) * (b : G)⁻¹ := by group
      rw [e]
      exact h2
  have hTM₁ : T ≤ M₁ := fun t ht => ⟨hTL ht, hT1 t ht⟩
  have h1 := Subgroup.relIndex_mul_relIndex T M₁ M hTM₁ inf_le_left
  have h2 := Subgroup.relIndex_mul_relIndex T M ⊤ hTL le_top
  rw [Subgroup.relIndex_top_right, Subgroup.relIndex_top_right] at h2
  apply hyp.sylow.2
  rw [← h2, ← h1]
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (by rw [Subgroup.relIndex, hidx]) _) _

end Hyp

end Sec121Swap

open Sec121Swap Sec121Thm

theorem setup121Swap_holds :
    ∀ (G : Type) [Group G] [Finite G] (T L V V₁ V₂ : Subgroup G) (n : ℕ),
      Hyp121 G T L V V₁ V₂ n → T ≤ Subgroup.normalizer (L : Set G) →
        ∃ t ∈ T, t ∉ L ⊔ pCoreOf 2 (L ⊔ T) ∧ V₂ = CFSG.conjugate V₁ t := by
  intro G _ _ T L V V₁ V₂ n hyp hTL
  have hVe := isElemAbelian_of_isPrimeReduced hyp.le hyp.reduced
  have := hVe.1
  obtain ⟨hcard₁, hcard₂, -⟩ := Sec1212.card_eq_of_hyp121 hyp
  obtain ⟨t, ht, ht1⟩ := exists_mem_not_normalizer hyp hTL
  have ht1' : t⁻¹ ∉ Subgroup.normalizer (V₁ : Set G) := fun h =>
    ht1 (by simpa using Subgroup.inv_mem _ h)
  have hswap := (swap_of_hyp121 hyp (Subgroup.inv_mem _ (hTL ht)) ht1').1
  have hLQ : L ⊔ pCoreOf 2 (L ⊔ T) ≤ Subgroup.normalizer (V₁ : Set G) := by
    refine sup_le hyp.norm₁ ?_
    rw [setup121Q_holds G T L V V₁ V₂ n hyp hTL]
    have hV₁V : V₁ ≤ V := hyp.sup ▸ le_sup_left
    exact inf_le_right.trans ((Subgroup.centralizer_le (by exact_mod_cast hV₁V)).trans
      (Subgroup.centralizer_le_normalizer _))
  refine ⟨t, ht, fun h => ht1 (hLQ h), ?_⟩
  have hle : CFSG.conjugate V₁ t ≤ V₂ := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    simpa [MulAut.conj_apply] using hswap y hy
  have hcard : Nat.card ↥(CFSG.conjugate V₁ t) = Nat.card ↥V₁ :=
    Subgroup.card_map_of_injective (MulAut.conj t⁻¹).injective
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hcard, hcard₁, hcard₂]

end CFSG.Quasithin.H13
