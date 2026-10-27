module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellShort
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1NmB

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Lem1211NormalBlk : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V V₁ V₂ : Subgroup G) (n : ℕ) (β : G → G → ZMod 2),
    Hyp121 G T L V V₁ V₂ n → T ≤ Subgroup.normalizer (L : Set G) →
    IsDualPairing121 L V₁ V₂ β → ∀ v ∈ V, IsNonsingular121 V₁ V₂ β v →
      CharTwo (Subgroup.centralizer ({v} : Set G)) →
      Subgroup.centralizer ({v} : Set G) ≤
        Subgroup.normalizer (oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G)) : Set G) →
      ∀ B : Subgroup G, IsChi0Block (centralizerSection (Subgroup.centralizer ({v} : Set G))
          (oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G)))
          (pCoreOf 2 (oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))))) B →
        Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (B : Set G)

@[expose] def Lem1211NormalLin : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B B₀ P : Subgroup G) (k : ℕ), IsShort2 B → 1 < k →
    IsLin2Type B k → B₀ ≤ B → IsBorelOfBlock B B₀ → IsPGroup 2 P →
    P ≤ Subgroup.normalizer (B : Set G) → P ≤ Subgroup.centralizer (B₀ : Set G) →
    P ≤ Subgroup.centralizer (pCoreOf 2 B : Set G) → P ≤ Subgroup.centralizer (B : Set G)

@[expose] def Lem1211NormalA318 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V V₁ V₂ : Subgroup G) (n : ℕ),
    Hyp121 G T L V V₁ V₂ n → T ≤ Subgroup.normalizer (L : Set G) →
      ∀ x ∈ Subgroup.normalizer (L : Set G), (∃ k : ℕ, orderOf x = 3 ^ k) → x ∈ L

@[expose] def Lem1211NormalMax : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V V₁ V₂ : Subgroup G) (n : ℕ) (β : G → G → ZMod 2),
    Hyp121 G T L V V₁ V₂ n → T ≤ Subgroup.normalizer (L : Set G) →
    IsDualPairing121 L V₁ V₂ β → ∀ v ∈ V, IsNonsingular121 V₁ V₂ β v →
      IsMaxSubgroupIn (L ⊔ T) ((L ⊔ T) ⊓ Subgroup.centralizer ({v} : Set G))

namespace Sec1211Ns

theorem mul_pow_mem_of_mem {G : Type} [Group G] {N : Subgroup G} {l y : G} (hl : l ∈ N)
    (hy : y ∈ Subgroup.normalizer (N : Set G)) (j : ℕ) : (l * y) ^ j * (y ^ j)⁻¹ ∈ N := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 : y ^ j * l * (y ^ j)⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hy j) l).mp hl
    have e : (l * y) ^ (j + 1) * (y ^ (j + 1))⁻¹ =
        ((l * y) ^ j * (y ^ j)⁻¹) * (y ^ j * l * (y ^ j)⁻¹) := by
      rw [pow_succ, pow_succ]
      group
    rw [e]
    exact N.mul_mem ih h1

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ} {a₀ c₀ : G}
  {S : Setting T L V V₁ V₂ n a₀ c₀} {m : ℕ}

variable (S) in
include S in
theorem lv_eq_oTwoUpper :
    Sec1216Lv.lv L (a₀ * c₀) = oTwoUpper (L ⊓ Subgroup.centralizer ({a₀ * c₀} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := L ⊓ Subgroup.centralizer ({a₀ * c₀} : Set G) with hX
  set Lv := Sec1216Lv.lv L (a₀ * c₀) with hLv
  have hLvX : Lv ≤ X := perfectCore_le X
  have hLvn : (Lv.subgroupOf X).Normal := perfectCore_normal X
  have hpow : ∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k ∈ Lv := by
    intro x hx
    have hρ : S.C₁.ρ ⟨x, hx.1⟩ ∈ PairStab.pairStab (S.C₁.E a₀) (S.C₂.E c₀) :=
      (S.mem_centralizer_iff ⟨x, hx.1⟩).mp hx.2
    obtain ⟨l, hl, hlx⟩ := S.exists_mem_lv hρ
    obtain ⟨ι⟩ := S.hyp.iso
    have hker : l⁻¹ * ⟨x, hx.1⟩ ∈ CFSG.pCore 2 ↥L := by
      rw [← S.C₁.ker_eq S.hn ι, MonoidHom.mem_ker, map_mul, map_inv, hlx, inv_mul_cancel]
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, hker⟩
    refine ⟨k, ?_⟩
    have hk' : ((l : G)⁻¹ * x) ^ 2 ^ k = 1 := by
      have := congrArg (fun y : ↥(CFSG.pCore 2 ↥L) => ((y : ↥L) : G)) hk
      simpa using this
    have hlX : (l : G) ∈ X := hLvX hl
    have hXN : X ≤ Subgroup.normalizer (Lv : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLvX).mp hLvn
    have hyX : (l : G)⁻¹ * x ∈ X := X.mul_mem (X.inv_mem hlX) hx
    have h1 := mul_pow_mem_of_mem hl (hXN hyX) (2 ^ k)
    rw [show (l : G) * ((l : G)⁻¹ * x) = x by group, hk', inv_one, mul_one] at h1
    exact h1
  refine le_antisymm ?_ (oTwoUpper_le_of_pow_mem hpow)
  have hperf : ⁅Lv, Lv⁆ = Lv := Sec1216Lv.lv_perfect L _
  have heq := C2Nine.eq_of_perfect_of_pow_mem hperf (inf_le_left : Lv ⊓ oTwoUpper X ≤ Lv)
    ⟨fun y hy l => by
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      exact ⟨Lv.mul_mem (Lv.mul_mem l.2 hy.1) (Lv.inv_mem l.2),
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper X (hLvX l.2)) _).mp hy.2⟩⟩
    fun y hy => by
      obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper X (hLvX hy)
      exact ⟨k, Lv.pow_mem hy _, hk⟩
  exact heq ▸ inf_le_right

variable (S) in
include S in
theorem isUniqueM_sup (h331 : Stmt3_3_1) :
    IsUniqueM (L ⊔ T) (Subgroup.normalizer (L : Set G)) := by
  have hqs := Sec121Thm.isQuasisimple_of_hyp121 S.hyp
  have hLT : conjClosure L T = L :=
    le_antisymm (conjClosure_le fun t ht l hl =>
      (Subgroup.mem_normalizer_iff.mp (S.hTL ht) l).mp hl) (le_conjClosure L T)
  obtain ⟨⟨hMmax, -, huniqLT⟩, -⟩ :=
    (h331 G T S.hyp.simple S.hyp.nonabelian S.hyp.qtke S.hyp.sylow).2 L S.hyp.maximal hqs
  rw [hLT] at hMmax huniqLT
  exact ⟨⟨hMmax, sup_le Subgroup.le_normalizer S.hTL⟩, fun M' hM' => huniqLT M' hM'.1 hM'.2⟩

variable (S) in
include S in
theorem centralizer_V_le (h331 : Stmt3_3_1) :
    Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmax := (S.isUniqueM_sup h331).1.1
  have hV2 : IsPGroup 2 ↥V := fun x => ⟨1, Subtype.ext (by simpa using S.hVe.2 x x.2)⟩
  have hV1 : V ≠ ⊥ := Sec121Thm.ne_bot_of_hyp121 S.hyp
  have hNV : Subgroup.normalizer (V : Set G) = Subgroup.normalizer (L : Set G) :=
    hmax.2 _ ⟨V, hV1, hV2, rfl⟩ S.le_normalizer
  rw [← hNV]
  exact Subgroup.centralizer_le_normalizer _

theorem false_of_lin (h331 : Stmt3_3_1) (hLin : Lem1211NormalLin) (F : Frame S m) (hm : 3 ≤ m)
    {B : Subgroup G}
    (hQY : IsSylowTwoOf (T ⊓ Subgroup.centralizer (V : Set G))
      (centralizerSection (Subgroup.centralizer ({a₀ * c₀} : Set G))
        (Sec1216Lv.lv L (a₀ * c₀)) (pCoreOf 2 (Sec1216Lv.lv L (a₀ * c₀)))))
    (hB : IsChi0Block (centralizerSection (Subgroup.centralizer ({a₀ * c₀} : Set G))
        (Sec1216Lv.lv L (a₀ * c₀)) (pCoreOf 2 (Sec1216Lv.lv L (a₀ * c₀)))) B)
    {k : ℕ} (hk : 1 < k) (hlin : IsLin2Type B k)
    (hBor : IsBorelOfBlock B (B ⊓ (centralizerSection (Subgroup.centralizer ({a₀ * c₀} : Set G))
        (Sec1216Lv.lv L (a₀ * c₀)) (pCoreOf 2 (Sec1216Lv.lv L (a₀ * c₀))) ⊓
        Subgroup.normalizer (L : Set G))))
    (hBn : Subgroup.centralizer ({a₀ * c₀} : Set G) ≤ Subgroup.normalizer (B : Set G))
    (hBM : ¬ B ≤ Subgroup.normalizer (L : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := centralizerSection (Subgroup.centralizer ({a₀ * c₀} : Set G))
    (Sec1216Lv.lv L (a₀ * c₀)) (pCoreOf 2 (Sec1216Lv.lv L (a₀ * c₀))) with hY
  have hV2 : IsPGroup 2 ↥V := fun x => ⟨1, Subtype.ext (by simpa using S.hVe.2 x x.2)⟩
  have hVH : V ≤ Subgroup.centralizer ({a₀ * c₀} : Set G) := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact S.comm hx S.v_mem
  have hVB₀ : V ≤ Subgroup.centralizer ((B ⊓ (Y ⊓ Subgroup.normalizer (L : Set G)) :
      Subgroup G) : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxC := mem_centralizer_V_of_mem_Y F hm hx.2.2 hx.2.1
    exact (Subgroup.mem_centralizer_iff.mp hxC w hw).symm
  have hO₂B : pCoreOf 2 B ≤ T ⊓ Subgroup.centralizer (V : Set G) :=
    (Setup.Campbell.pCoreOf_le_of_isSubnormal 2 hB.1.2.1 hB.1.2.2).trans
      (B6.pCoreOf_two_le_of_isSylowTwoOf hQY)
  have hVO : V ≤ Subgroup.centralizer ((pCoreOf 2 B : Subgroup G) : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hO₂B hx).2 w hw).symm
  have hVcB := hLin G B (B ⊓ (Y ⊓ Subgroup.normalizer (L : Set G))) V k hB.1.1 hk hlin
    inf_le_left hBor hV2 (hVH.trans hBn) hVB₀ hVO
  apply hBM
  refine le_trans ?_ (S.centralizer_V_le h331)
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact (Subgroup.mem_centralizer_iff.mp (hVcB hw) b hb).symm

end Setting

end Sec1211Ns

end CFSG.Quasithin.H13
