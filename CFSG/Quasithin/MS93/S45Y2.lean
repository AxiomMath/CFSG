module

public import CFSG.Quasithin.MS93.S45Y1
public import CFSG.Quasithin.MS93.S45Inputs
public import CFSG.Quasithin.MS93.S45X4

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {𝔾 : Type} [Group 𝔾]

theorem le_normalizer_commutator {K A B : Subgroup 𝔾} (hA : K ≤ Subgroup.normalizer (A : Set 𝔾))
    (hB : K ≤ Subgroup.normalizer (B : Set 𝔾)) :
    K ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup 𝔾) : Set 𝔾) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ g ∈ K, ⁅A, B⁆.map (MulAut.conj g).toMonoidHom ≤ ⁅A, B⁆ := by
    intro g hg
    rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer (hA hg),
      map_conj_eq_of_mem_normalizer (hB hg)]
  intro y
  constructor
  · intro hy; exact key g hg ⟨y, hy, rfl⟩
  · intro hy
    have := key g⁻¹ (inv_mem hg) ⟨_, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using this

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

section GoodPath

variable {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}

theorem case13_vertex (h14 : MS14AS) (hSQ : SQTKQuot) (hZV : c.HZV) (hQ4 : c.HQ4)
    (hQ2b : c.HQ2b) (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a) (h34 : 34 ≤ a)
    (haN : a + 30 ≤ N)
    {ψ : ↥(stab (puAmalgam c.hyp.le) (p a)) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab _ (p a)) (Uloc c.hyp.le L (p a)) ⊥ ψ false 1)
    (hT : natImage ψ (Qv (puAmalgam c.hyp.le) (p (a + 1))) = rootGroup 1 0 ⊔ rootGroup 2 0) :
    ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ⊓
        Subgroup.centralizer (Ltil c.hyp.le L (p a) : Set _) = Hloc c.hyp.le L (p a) ∧
      centerOf ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ =
        Uloc c.hyp.le L (p a) ⊔ Hloc c.hyp.le L (p a) ∧
      ⁅centerOf ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆,
        Ltil c.hyp.le L (p a)⁆ = Uloc c.hyp.le L (p a) ∧
      IsSumOfNaturalModulesVia (stab _ (p a))
        (frattiniIn ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆)
        (centerOf ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆) ψ true 1 ∧
      IsSumOfNaturalModulesVia (stab _ (p a))
        (⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ⊓ Subgroup.centralizer
          (frattiniIn ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ : Set _))
        (frattiniIn ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆) ψ true 2 ∧
      IsSumOfNaturalModulesVia (stab _ (p a))
        ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆
        (⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ⊓ Subgroup.centralizer
          (frattiniIn ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ : Set _)) ψ
        false 2 := by
  have h := c.hyp
  have h20 := h.hyp20
  have : CharP F 2 := c.charP
  obtain ⟨k, rfl⟩ : ∃ k, a = k + 34 := ⟨a - 34, by omega⟩
  have hk : Even k := (Nat.even_add.mp ha).mpr (by decide)
  have hα := c.isMVtx_of_isGoodPath hp (k := k + 34) (by omega) ha
  obtain ⟨p', hp', hpp', hU1, hU3⟩ := c.exists_branch hp ha (by omega) (by omega)
  obtain ⟨hB1, hB2, hB3, hB4, hB5⟩ := hQ2b p p' N hp hp' (k + 34) ha h34 haN hpp' hU1 hU3
  set Qα := Qv (puAmalgam h.le) (p (k + 34)) with hQα
  set Lt := Ltil h.le L (p (k + 34)) with hLt
  set V := ⁅Qα, Lt⁆ with hV
  set U := Uloc h.le L (p (k + 34)) with hU
  set H := Hloc h.le L (p (k + 34)) with hH
  set Z := ZM (puAmalgam h.le) (p (k + 34)) with hZ
  set Vc := Vcirc h.le L (p (k + 34)) with hVc
  set Vh := Vc ⊔ Z with hVh
  set Wh := whv h (p (k + 34)) (p (k + 34 + 2)) with hWh
  set X₁ := conjCl (stab (puAmalgam h.le) (p (k + 34)))
    (Vcirc h.le L (p (k + 34 + 4)) ⊔ ZM _ (p (k + 34 + 4))) ⊔ Wh with hX₁
  set X₂ := conjCl (stab (puAmalgam h.le) (p (k + 34)))
    (Vcirc h.le L (p' (k + 34 + 4)) ⊔ ZM _ (p' (k + 34 + 4))) ⊔ Wh with hX₂
  set X₁' := ⁅X₁, stab (puAmalgam h.le) (p (k + 34))⁆ ⊔ Wh with hX₁'
  set X₂' := ⁅X₂, stab (puAmalgam h.le) (p (k + 34))⁆ ⊔ Wh with hX₂'
  have hpa : p' (k + 34) = p (k + 34) := hpp' (k + 34) (by omega)
  have hpa2 : p' (k + 34 + 2) = p (k + 34 + 2) := hpp' (k + 34 + 2) (by omega)
  have hpam : p' (k + 34 - 2) = p (k + 34 - 2) := hpp' (k + 34 - 2) (by omega)
  have hγ := c.isMVtx_of_isGoodPath hp (k := k + 34 + 2) (by omega) (ha.add even_two)
  have hQs : Qα ≤ stab (puAmalgam h.le) (p (k + 34)) := qv_le_stab _ _
  have hKQ : stab (puAmalgam h.le) (p (k + 34)) ≤ Subgroup.normalizer (Qα : Set _) :=
    stab_le_normalizer_qv _ _
  have hLs : Lt ≤ stab (puAmalgam h.le) (p (k + 34)) := ltil_le_stab h _
  have hKL : stab (puAmalgam h.le) (p (k + 34)) ≤ Subgroup.normalizer (Lt : Set _) :=
    stab_le_normalizer_ltil h _
  have hKV : stab (puAmalgam h.le) (p (k + 34)) ≤ Subgroup.normalizer (V : Set _) :=
    le_normalizer_commutator hKQ hKL
  have hVQ : V ≤ Qα := Subgroup.le_normalizer_iff_commutator_le_left.mp (hLs.trans hKQ)
  have hKU : stab (puAmalgam h.le) (p (k + 34)) ≤ Subgroup.normalizer (U : Set _) := hψ.1
  have hKZ : stab (puAmalgam h.le) (p (k + 34)) ≤ Subgroup.normalizer (Z : Set _) :=
    stab_le_normalizer_zm _ _
  have hKVc : stab (puAmalgam h.le) (p (k + 34)) ≤ Subgroup.normalizer (Vc : Set _) :=
    c.stab_le_normalizer_vcirc _
  have hKVh : stab (puAmalgam h.le) (p (k + 34)) ≤ Subgroup.normalizer (Vh : Set _) :=
    le_normalizer_sup hKVc hKZ
  have hKWh : stab (puAmalgam h.le) (p (k + 34)) ≤ Subgroup.normalizer (Wh : Set _) :=
    S4A.le_normalizer_conjCl _ _
  have hZQ : Z ≤ Qα := zm_le_qv_of_dist_lt _ hα (by simp [c.b8])
  have hVvQ : Vv (puAmalgam h.le) (p (k + 34)) ≤ Qα := c.vv_le_qv' hα
  have hUZ : U ≤ Z := uloc_le_zm h c.full hα
  have hZloc : Zloc h.le L (p (k + 34)) ≤ Z := zloc_le_zm h c.full hα
  have hZc := zloc_le_centralizer_stab h c.full hα
  have hUL : ⁅U, Lt⁆ = U := c.commutator_uloc_ltil hα
  have hUVc : U ≤ Vc := by
    rw [← hUL]
    exact Subgroup.commutator_mono (hUZ.trans (le_sup_right.trans (c.vhat_le_vv hα))) le_rfl
  have hVcV : Vc ≤ V := Subgroup.commutator_mono hVvQ le_rfl
  have hUV : U ≤ V := hUVc.trans hVcV
  have hHV : H ≤ V := (Subgroup.commutator_mono hVcV le_rfl).trans
    (Subgroup.le_normalizer_iff_commutator_le_left.mp (hQs.trans hKV))
  have hHZ : H ≤ Zloc h.le L (p (k + 34)) :=
    (Subgroup.commutator_mono (c.vcirc_le_vv _) le_rfl).trans (c.commutator_vv_qv_le_zloc hα)
  have hHVc : H ≤ Vc :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hQs.trans hKVc)
  have hZcen : Z ≤ Subgroup.centralizer (Qα : Set _) := zm_le_centralizer_qv _ h20 hα
  have hF4 : V ⊓ Subgroup.centralizer (Lt : Set _) = H := by
    refine le_antisymm hB1 (le_inf hHV ?_)
    exact (hHZ.trans hZc).trans (Subgroup.centralizer_le hLs)
  have hF3 : centerOf V = U ⊔ H := by
    refine le_antisymm hB2 (le_inf (sup_le hUV hHV) ?_)
    exact (sup_le hUZ (hHZ.trans hZloc)).trans (hZcen.trans (Subgroup.centralizer_le hVQ))
  have hZsplit : Z = U ⊔ Zloc h.le L (p (k + 34)) := zm_eq_uloc_sup_zloc h c.full hα
  have hUn : U ≤ Subgroup.normalizer (Zloc h.le L (p (k + 34)) : Set _) :=
    (hUZ.trans (hZQ.trans hQs)).trans (c.stab_le_normalizer_of_le_centralizer hZc)
  have hVZ : V ⊓ Z ≤ U ⊔ H := by
    rw [hZsplit, inf_comm, sup_inf_eq_of_le hUV hUn]
    refine sup_le_sup_left ?_ _
    rw [← hF4]
    exact le_inf inf_le_right (inf_le_left.trans (hZc.trans (Subgroup.centralizer_le hLs)))
  have hF11 : Vc ⊓ Z = U ⊔ H :=
    le_antisymm ((inf_le_inf_right _ hVcV).trans hVZ)
      (le_inf (sup_le hUVc hHVc) (sup_le hUZ (hHZ.trans hZloc)))
  have hF10 : V ⊓ Vh = Vc := by
    refine le_antisymm ?_ (le_inf hVcV le_sup_left)
    rw [inf_comm, sup_inf_eq_of_le hVcV (hVcV.trans (hVQ.trans (hQs.trans hKZ)))]
    exact sup_le le_rfl ((inf_comm Z V ▸ hVZ).trans (sup_le hUVc hHVc))
  obtain ⟨d, hd⟩ := c.exists_isSum_vhat hα hψs hψ
  have hdB := c.isSum_bloc hα hd
  have hdt := c.dual_eq_true hp (x := k + 28) (hk.add (by decide)) (by omega) (by omega) hψs hψ hdB
  subst hdt
  have hWhQ : Wh ≤ Qα := conjCl_le_of_le_normalizer ((c.vhat_le_vv hγ).trans (vi_le_qv _ (by
    rw [tdist_comm, hp.dist_eq' (i := k + 34) (j := k + 34 + 2) (by omega) (by omega), c.b8]
    omega))) hKQ
  have hVhWh : Vh ≤ Wh := c.vhat_le_whv' hZV hp ha (by omega) (by omega)
  obtain ⟨hsup2, hinf2, h₁m, h₂m⟩ :=
    c.mid_layer h14 hSQ hZV hQ4 hp ha (by omega) (by omega) hp' hpp' hU1 hU3 hψs hψ hT
  have hL2 : IsSumOfNaturalModulesVia (stab (puAmalgam h.le) (p (k + 34))) Wh Vh ψ true 2 :=
    S46.isSumOfNaturalModulesVia_two h₁m h₂m hKWh ((hWhQ.trans hQs).trans h₁m.1)
      ((hWhQ.trans hQs).trans h₂m.1) hinf2 hsup2
  obtain ⟨hinf3, h₁t, h₂t⟩ := c.top_layer h14 hSQ hZV hQ4 hp ha h34 haN hp' hpp' hU1 hU3 hψs hψ
  have hμ := c.isMVtx_of_isGoodPath hp (k := k + 34 + 4) (by omega) (ha.add (by decide))
  have hμ' := c.isMVtx_of_isGoodPath hp' (k := k + 34 + 4) (by omega) (ha.add (by decide))
  have hX₁Q : X₁ ≤ Qα := by
    refine sup_le (conjCl_le_of_le_normalizer ((c.vhat_le_vv hμ).trans (vi_le_qv _ ?_)) hKQ)
      hWhQ
    rw [tdist_comm, hp.dist_eq' (i := k + 34) (j := k + 34 + 4) (by omega) (by omega), c.b8]
    omega
  have hX₂Q : X₂ ≤ Qα := by
    refine sup_le (conjCl_le_of_le_normalizer ((c.vhat_le_vv hμ').trans (vi_le_qv _ ?_)) hKQ)
      hWhQ
    rw [← hpa, tdist_comm, hp'.dist_eq' (i := k + 34) (j := k + 34 + 4) (by omega) (by omega),
      c.b8]
    omega
  have hX₁s : X₁ ≤ stab (puAmalgam h.le) (p (k + 34)) := hX₁Q.trans hQs
  have hX₂s : X₂ ≤ stab (puAmalgam h.le) (p (k + 34)) := hX₂Q.trans hQs
  have hX₁'X₁ : X₁' ≤ X₁ := sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp
    (le_normalizer_sup (S4A.le_normalizer_conjCl _ _) hKWh)) le_sup_right
  have hX₂'X₂ : X₂' ≤ X₂ := sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp
    (le_normalizer_sup (S4A.le_normalizer_conjCl _ _) hKWh)) le_sup_right
  have hL3 : IsSumOfNaturalModulesVia (stab (puAmalgam h.le) (p (k + 34))) (X₁' ⊔ X₂') Wh ψ
      false 2 :=
    S46.isSumOfNaturalModulesVia_two h₁t h₂t (le_normalizer_sup h₁t.1 h₂t.1)
      ((sup_le (hX₁'X₁.trans hX₁s) (hX₂'X₂.trans hX₂s)).trans h₁t.1)
      ((sup_le (hX₁'X₁.trans hX₁s) (hX₂'X₂.trans hX₂s)).trans h₂t.1) hinf3 rfl
  have hKX₁' : stab (puAmalgam h.le) (p (k + 34)) ≤ Subgroup.normalizer (X₁' : Set _) := h₁t.1
  have hKX₂' : stab (puAmalgam h.le) (p (k + 34)) ≤ Subgroup.normalizer (X₂' : Set _) := h₂t.1
  have hKXt : stab (puAmalgam h.le) (p (k + 34)) ≤ Subgroup.normalizer ((X₁' ⊔ X₂' :
      Subgroup _) : Set _) := le_normalizer_sup hKX₁' hKX₂'
  have hF9 : (V ⊓ Wh) ⊔ Vh = Wh := by
    refine le_antisymm (sup_le inf_le_right hVhWh) ?_
    refine (show Wh ≤ _ from hsup2.symm.le).trans (sup_le ?_ ?_)
    · rw [← c.sup_inf_eq_of_dual hα hψs hψ h₁m hKV (Subgroup.commutator_mono
        ((le_sup_left.trans hsup2.le).trans hWhQ) le_rfl)]
      exact sup_le_sup_right (inf_le_inf_left _ (le_sup_left.trans hsup2.le)) _
    · rw [← c.sup_inf_eq_of_dual hα hψs hψ h₂m hKV (Subgroup.commutator_mono
        ((le_sup_right.trans hsup2.le).trans hWhQ) le_rfl)]
      exact sup_le_sup_right (inf_le_inf_left _ (le_sup_right.trans hsup2.le)) _
  have hV6 : X₁ ⊔ X₂ ≤ conjCl (stab (puAmalgam h.le) (p (k + 34)))
      (whv h (p (k + 34 + 2)) (p (k + 34))) := by
    have e : whv h (p (k + 34 + 2)) (p (k + 34 + 4)) = whv h (p (k + 34 + 2)) (p (k + 34)) :=
      c.whv_eq_of_isGoodPath hp (a := k + 34 + 2) (ha.add even_two) (by omega) (by omega)
    have hγγ : Vcirc h.le L (p (k + 34 + 2)) ⊔ ZM _ (p (k + 34 + 2)) ≤
        whv h (p (k + 34 + 2)) (p (k + 34)) := by
      rw [← e]; exact c.vhat_le_whv' hZV hp (a := k + 34 + 2) (ha.add even_two) (by omega)
        (by omega)
    have hμγ : Vcirc h.le L (p (k + 34 + 4)) ⊔ ZM _ (p (k + 34 + 4)) ≤
        whv h (p (k + 34 + 2)) (p (k + 34)) := by
      rw [← e]; exact c.vhat_le_whv_self
    have hμ'γ : Vcirc h.le L (p' (k + 34 + 4)) ⊔ ZM _ (p' (k + 34 + 4)) ≤
        whv h (p (k + 34 + 2)) (p (k + 34)) := by
      have e' : whv h (p' (k + 34 + 2)) (p' (k + 34 + 4)) =
          whv h (p' (k + 34 + 2)) (p' (k + 34)) :=
        c.whv_eq_of_isGoodPath hp' (a := k + 34 + 2) (ha.add even_two) (by omega) (by omega)
      rw [hpa, hpa2] at e'
      rw [← e']; exact c.vhat_le_whv_self
    have hWhγ : Wh ≤ conjCl (stab (puAmalgam h.le) (p (k + 34)))
        (whv h (p (k + 34 + 2)) (p (k + 34))) := conjCl_mono hγγ
    exact sup_le (sup_le (conjCl_mono hμγ) hWhγ) (sup_le (conjCl_mono hμ'γ) hWhγ)
  have hDD : ⁅X₁ ⊔ X₂, X₁ ⊔ X₂⁆ ≤ X₁' ⊔ X₂' :=
    ((Subgroup.commutator_mono hV6 hV6).trans
      (c.commutator_vsix_le hZV hQ4 hp ha h34 (by omega))).trans (le_sup_right.trans le_sup_left)
  have hDL : ⁅X₁ ⊔ X₂, Lt⁆ ≤ X₁' ⊔ X₂' := by
    refine S46.commutator_sup_le_of_le_normalizer hKXt hX₁s hX₂s ?_ ?_
    · exact ((Subgroup.commutator_mono le_rfl hLs).trans le_sup_left).trans le_sup_left
    · exact ((Subgroup.commutator_mono le_rfl hLs).trans le_sup_left).trans le_sup_right
  have hF7 : V ≤ X₁' ⊔ X₂' := by
    rw [hV, Subgroup.commutator_le]
    intro q hq l hl
    exact commutator_mem_of_perfect (S4A.ltil_perfect h hα)
      (sup_le (hX₁'X₁.trans le_sup_left) (hX₂'X₂.trans le_sup_right)) hDD hDL
      (fun l hl => hB5 (Subgroup.commutator_mem_commutator hq hl)) hl
  have hKVW : stab (puAmalgam h.le) (p (k + 34)) ≤ Subgroup.normalizer ((V ⊔ Wh : Subgroup _) :
      Set _) := le_normalizer_sup hKV hKWh
  have hstab : stab (puAmalgam h.le) (p (k + 34)) = Lt ⊔ Qα := stab_eq_ltil_sup_qv h c.full hα
  have hC1₁ := c.commutator_top_qv_le hZV hQ4 hp ha h34 (by omega)
  have hC1₂ := c.commutator_top_qv_le hZV hQ4 hp' ha h34 (by omega)
  rw [hpa, hpa2] at hC1₂
  have hXi : ∀ X : Subgroup (puAmalgam h.le).Universal, X ≤ Qα → ⁅X, Qα⁆ ≤ Wh →
      ⁅X, stab (puAmalgam h.le) (p (k + 34))⁆ ⊔ Wh ≤ V ⊔ Wh := by
    intro X hXQ hXW
    refine sup_le ?_ le_sup_right
    refine (Subgroup.commutator_mono le_rfl hstab.le).trans ?_
    rw [Subgroup.commutator_comm]
    refine S46.commutator_sup_le_of_le_normalizer hKVW hLs hQs ?_ ?_
    · rw [Subgroup.commutator_comm]
      exact (Subgroup.commutator_mono hXQ le_rfl).trans le_sup_left
    · rw [Subgroup.commutator_comm]
      exact hXW.trans le_sup_right
  have hF8 : V ⊔ Wh = X₁' ⊔ X₂' :=
    le_antisymm (sup_le hF7 (le_sup_right.trans le_sup_left))
      (sup_le (hXi X₁ hX₁Q hC1₁) (hXi X₂ hX₂Q hC1₂))
  have hWhC : Wh ≤ Subgroup.centralizer (Vc : Set _) :=
    (c.whv_le_centralizer_vv hγ (by
      rw [hp.dist_eq' (i := k + 34) (j := k + 34 + 2) (by omega) (by omega)]; omega)).trans
      (Subgroup.centralizer_le (c.vcirc_le_vv _))
  have hF6 : V ⊓ Subgroup.centralizer (Vc : Set _) = V ⊓ Wh :=
    le_antisymm (le_inf inf_le_left hB4) (le_inf inf_le_left (inf_le_right.trans hWhC))
  have hVhn : Vh ≤ Subgroup.normalizer (Z : Set _) :=
    (sup_le (c.vcirc_le_vv _ |>.trans hVvQ) hZQ).trans (hQs.trans hKZ)
  refine ⟨hF4, hF3, ?_, ?_, ?_, ?_⟩
  ·
    rw [hF3]
    refine le_antisymm ?_ (hUL.symm.le.trans (Subgroup.commutator_mono le_sup_left le_rfl))
    refine S46.commutator_sup_le_of_le_normalizer hKU (hUZ.trans (hZQ.trans hQs))
      (hHV.trans (hVQ.trans hQs)) hUL.le ?_
    rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr
      ((hHZ.trans hZc).trans (Subgroup.centralizer_le hLs))]
    exact bot_le
  ·
    rw [hB3, hF3, ← hF11]
    exact S4A.isSumOfNaturalModulesVia_transfer hd (sup_eq_left.mpr le_sup_right)
      (inf_eq_right.mpr le_sup_right) le_sup_left rfl hKVc hKZ hVhn
  ·
    rw [hB3, hF6]
    have h1 := S4A.isSumOfNaturalModulesVia_transfer hL2 (sup_eq_left.mpr hVhWh)
      (inf_eq_right.mpr hVhWh) inf_le_right hF9 (le_normalizer_inf hKV hKWh) hKVh
      ((hWhQ.trans hQs).trans hKVh)
    have e : V ⊓ Wh ⊓ Vh = Vc := by
      rw [inf_assoc, inf_eq_right.mpr hVhWh, hF10]
    rwa [e] at h1
  ·
    rw [hB3, hF6]
    exact S4A.isSumOfNaturalModulesVia_transfer hL3
      (sup_eq_left.mpr (le_sup_right.trans le_sup_left))
      (inf_eq_right.mpr (le_sup_right.trans le_sup_left)) hF7 hF8 hKV hKWh
      ((sup_le (hX₁'X₁.trans hX₁s) (hX₂'X₂.trans hX₂s)).trans hKWh)

end GoodPath

end Ctx

end CFSG.Quasithin.MS93.S45
