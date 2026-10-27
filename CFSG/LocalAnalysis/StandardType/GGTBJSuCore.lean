module

public import CFSG.LocalAnalysis.StandardType.GGTBJSuBlock
public import CFSG.LocalAnalysis.StandardType.GGTBJSuDefs
public import CFSG.LocalAnalysis.StandardType.GGTBJSuCoreAux
public import CFSG.RankThree.Classical2.UnitarySplitPrimeRank
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  UCoord UModel
open CFSG.SectionRank.OddCover (diagHom)

theorem ggTBJ_su_core {K : Type} [Field K] [Finite K] {n d p : ℕ} {u : Kˣ}
    (h : UnitaryFieldData 2 n K) [NeZero p] (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 2 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1) (hd : 4 ≤ d) (hpd : ¬ p ∣ d)
    (hu : u ^ p = 1) (huq : u ^ (2 ^ n + 1) = 1) (hord : orderOf u = p)
    {G : Type} [Group G] [Finite G] (ψ : ↥(unitarySU 2 n K d) →* G)
    (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 n K d))
    (f₀ : ↥(sumZero d p)) {J : Subgroup G}
    (hJ : CFSG.Assembly.IsComponentOf J (ψ.range ⊓
      Subgroup.centralizer ({ψ (ggTBJSuD h hu huq hord f₀)} : Set G)))
    (hcount : p ^ 2 * Nat.card {f : ↥(sumZero d p) //
        ∀ j ∈ J, ψ (ggTBJSuD h hu huq hord f) * j = j * ψ (ggTBJSuD h hu huq hord f)} ≤
      p ^ (d - 1)) :
    ∃ (n₁ n₂ : G) (s₁ s₂ : MulAut ↥(sumZero d p)), n₁ ∈ J ∧ n₂ ∈ J ∧
      (∀ f, n₁ * ψ (ggTBJSuD h hu huq hord f) * n₁⁻¹ = ψ (ggTBJSuD h hu huq hord (s₁ f))) ∧
      (∀ f, n₂ * ψ (ggTBJSuD h hu huq hord f) * n₂⁻¹ = ψ (ggTBJSuD h hu huq hord (s₂ f))) ∧
      s₁ ^ 2 = 1 ∧ s₂ ^ 2 = 1 ∧
      Nat.card {f : ↥(sumZero d p) // s₁ f = f} * p = p ^ (d - 1) ∧
      Nat.card {f : ↥(sumZero d p) // s₂ f = f} * p = p ^ (d - 1) ∧ s₁ * s₂ ≠ s₂ * s₁ := by
  let t : Fin d → Kˣ := uvec hu f₀
  have hDt : diagHom d t ∈ unitarySU 2 n K d := (ggTBJSuD h hu huq hord f₀).2
  have hJ' : CFSG.Assembly.IsComponentOf J
      (ψ.range ⊓ Subgroup.centralizer ({ψ ⟨diagHom d t, hDt⟩} : Set G)) := hJ
  obtain ⟨I, hIt, hswap, hcent⟩ := ggTBJ_su_blockData hK hn ψ hker t hDt hJ'
  have hI3 : 3 ≤ I.card := by
    let C : Set ↥(sumZero d p) :=
      {f | ∀ j ∈ J, ψ (ggTBJSuD h hu huq hord f) * j = j * ψ (ggTBJSuD h hu huq hord f)}
    have hS0_le_C : ∀ f ∈ ggTBJsuC_S0 (p := p) I, f ∈ C := by
      intro f hf j hj
      have hconst : ∀ i ∈ I, ∀ j ∈ I, uvec hu f i = uvec hu f j := by
        intro i hi j hj
        rw [uvec_apply, uvec_apply, hf i hi j hj]
      exact hcent (uvec hu f) hconst (ggTBJSuD h hu huq hord f).2 j hj
    have hcard_le : Nat.card ↥(ggTBJsuC_S0 (p := p) I) ≤ Nat.card C := by
      exact Nat.card_mono (Set.toFinite _) (fun f hf => hS0_le_C f hf)
    by_contra hlt
    push Not at hlt
    have hIle2 : I.card ≤ 2 := by omega
    by_cases hIempty : I = ∅
    · have hS0_top : ggTBJsuC_S0 (p := p) I = ⊤ := by
        ext f
        simp [ggTBJsuC_S0, hIempty]
      have hS0_card : Nat.card ↥(ggTBJsuC_S0 (p := p) I) = p ^ (d - 1) := by
        rw [hS0_top, Subgroup.card_top, ggTBRowPerm_card_sumZero']
      have hC_ge : p ^ (d - 1) ≤ Nat.card C := by
        rw [← hS0_card]
        exact hcard_le
      have hle : p ^ 2 * p ^ (d - 1) ≤ p ^ (d - 1) := by
        calc p ^ 2 * p ^ (d - 1) ≤ p ^ 2 * Nat.card C := Nat.mul_le_mul_left _ hC_ge
          _ ≤ p ^ (d - 1) := hcount
      have hlt : p ^ (d - 1) < p ^ 2 * p ^ (d - 1) := by
        calc p ^ (d - 1) = 1 * p ^ (d - 1) := by rw [one_mul]
          _ < p ^ 2 * p ^ (d - 1) := by
            exact Nat.mul_lt_mul_of_pos_right (Nat.one_lt_pow (by omega) hp.one_lt)
              (pow_pos hp.pos _)
      exact absurd hle (not_le.mpr hlt)
    · have hS0_ge : p ^ (d - I.card) ≤ Nat.card ↥(ggTBJsuC_S0 (p := p) I) :=
        ggTBJsuC_card_S0_ge hp (Finset.nonempty_iff_ne_empty.mpr hIempty)
      have hC_ge : p ^ (d - I.card) ≤ Nat.card C := hS0_ge.trans hcard_le
      have hcontra : p ^ 2 * p ^ (d - I.card) ≤ p ^ (d - 1) := by
        calc p ^ 2 * p ^ (d - I.card) ≤ p ^ 2 * Nat.card C := Nat.mul_le_mul_left _ hC_ge
          _ ≤ p ^ (d - 1) := hcount
      have hpow : p ^ 2 * p ^ (d - I.card) = p ^ (2 + (d - I.card)) := by rw [← pow_add]
      rw [hpow] at hcontra
      have hle_exp : 2 + (d - I.card) ≤ d - 1 := (Nat.pow_le_pow_iff_right hp.one_lt).mp hcontra
      have hge_d : d ≤ 2 + (d - I.card) := by omega
      omega
  have hpos1 : 0 < I.card := Nat.lt_of_lt_of_le (by norm_num) hI3
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos1
  have hcard_erase_a : (I.erase a).card = I.card - 1 := Finset.card_erase_of_mem ha
  have hpos2 : 0 < (I.erase a).card := by
    rw [hcard_erase_a]
    exact Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by norm_num) hI3)
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hpos2
  have hbI : b ∈ I := Finset.mem_of_mem_erase hb
  have hba : b ≠ a := Finset.ne_of_mem_erase hb
  have hcard_erase_b : ((I.erase a).erase b).card = (I.erase a).card - 1 :=
    Finset.card_erase_of_mem hb
  have hpos3 : 0 < ((I.erase a).erase b).card := by
    rw [hcard_erase_b, hcard_erase_a, Nat.sub_sub]
    exact Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by norm_num : 2 < 3) hI3)
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hpos3
  have hcI : c ∈ I := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc)
  have hcb : c ≠ b := Finset.ne_of_mem_erase hc
  have hca : c ≠ a := by
    have hc' : c ∈ I.erase a := Finset.mem_of_mem_erase hc
    exact Finset.ne_of_mem_erase hc'
  obtain ⟨za, hzaGL, hzaJ⟩ := hswap a ha b hbI (Ne.symm hba)
  obtain ⟨zb, hzbGL, hzbJ⟩ := hswap b hbI c hcI (Ne.symm hcb)
  let n₁ : G := ψ za
  let n₂ : G := ψ zb
  let s₁ : MulAut ↥(sumZero d p) := permAutV (Equiv.swap a b)
  let s₂ : MulAut ↥(sumZero d p) := permAutV (Equiv.swap b c)
  refine ⟨n₁, n₂, s₁, s₂, hzaJ, hzbJ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    have hMD : za * ggTBJSuD h hu huq hord f * za⁻¹ =
        ggTBJSuD h hu huq hord (permAutV (Equiv.swap a b) f) := by
      apply Subtype.ext
      change ((za : GL (Fin d) K) * (ggTBJSuD h hu huq hord f : GL (Fin d) K) *
        (za : GL (Fin d) K)⁻¹) = diagHom d (uvec hu (permAutV (Equiv.swap a b) f))
      rw [hzaGL, ggTBJSuD_coe, uvec_permAutV]
      exact CFSG.RankThree.Classical2.permGL_mul_diagHom_mul_inv (Equiv.swap a b) (uvec hu f)
    calc n₁ * ψ (ggTBJSuD h hu huq hord f) * n₁⁻¹
        = ψ za * ψ (ggTBJSuD h hu huq hord f) * (ψ za)⁻¹ := rfl
      _ = ψ (za * ggTBJSuD h hu huq hord f * za⁻¹) := by rw [← map_inv, ← map_mul, ← map_mul]
      _ = ψ (ggTBJSuD h hu huq hord (permAutV (Equiv.swap a b) f)) := by rw [hMD]
  · intro f
    have hMD : zb * ggTBJSuD h hu huq hord f * zb⁻¹ =
        ggTBJSuD h hu huq hord (permAutV (Equiv.swap b c) f) := by
      apply Subtype.ext
      change ((zb : GL (Fin d) K) * (ggTBJSuD h hu huq hord f : GL (Fin d) K) *
        (zb : GL (Fin d) K)⁻¹) = diagHom d (uvec hu (permAutV (Equiv.swap b c) f))
      rw [hzbGL, ggTBJSuD_coe, uvec_permAutV]
      exact CFSG.RankThree.Classical2.permGL_mul_diagHom_mul_inv (Equiv.swap b c) (uvec hu f)
    calc n₂ * ψ (ggTBJSuD h hu huq hord f) * n₂⁻¹
        = ψ zb * ψ (ggTBJSuD h hu huq hord f) * (ψ zb)⁻¹ := rfl
      _ = ψ (zb * ggTBJSuD h hu huq hord f * zb⁻¹) := by rw [← map_inv, ← map_mul, ← map_mul]
      _ = ψ (ggTBJSuD h hu huq hord (permAutV (Equiv.swap b c) f)) := by rw [hMD]
  · change (permAutV (Equiv.swap a b)) ^ 2 = 1
    rw [pow_two, ← permAutV_mul, Equiv.swap_mul_self, permAutV_one]
  · change (permAutV (Equiv.swap b c)) ^ 2 = 1
    rw [pow_two, ← permAutV_mul, Equiv.swap_mul_self, permAutV_one]
  · change Nat.card {f : ↥(sumZero d p) // permAutV (Equiv.swap a b) f = f} * p = p ^ (d - 1)
    exact ggTBJsuC_card_fix_permAutV_swap hp hp2 (Ne.symm hba)
  · change Nat.card {f : ↥(sumZero d p) // permAutV (Equiv.swap b c) f = f} * p = p ^ (d - 1)
    exact ggTBJsuC_card_fix_permAutV_swap hp hp2 (Ne.symm hcb)
  · change (permAutV (Equiv.swap a b) * permAutV (Equiv.swap b c)) ≠
      (permAutV (Equiv.swap b c) * permAutV (Equiv.swap a b))
    intro h
    have hcoord := congrArg (fun (σ : MulAut ↥(sumZero d p)) => crd (σ (rootV a b)) b) h
    rw [MulAut.mul_apply, MulAut.mul_apply] at hcoord
    have h1 : crd (permAutV (Equiv.swap a b) (permAutV (Equiv.swap b c) (rootV a b))) b =
        (1 : ZMod p) := by
      rw [crd_permAutV, Equiv.swap_inv, Equiv.swap_apply_right, crd_permAutV, Equiv.swap_inv,
        Equiv.swap_apply_of_ne_of_ne (Ne.symm hba) (Ne.symm hca), crd_rootV_left (Ne.symm hba)]
    have h2 : crd (permAutV (Equiv.swap b c) (permAutV (Equiv.swap a b) (rootV a b))) b =
        (0 : ZMod p) := by
      rw [crd_permAutV, Equiv.swap_inv, Equiv.swap_apply_left, crd_permAutV, Equiv.swap_inv,
        Equiv.swap_apply_of_ne_of_ne hca hcb, crd_rootV_other hca hcb]
    rw [h1, h2] at hcoord
    have h1' : ((1 : ℕ) : ZMod p) = 0 := by simpa using hcoord
    exact hp.not_dvd_one ((ZMod.natCast_eq_zero_iff 1 p).mp h1')

end CFSG.StandardType

end
