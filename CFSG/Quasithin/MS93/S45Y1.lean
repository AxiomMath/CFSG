module

public import CFSG.Quasithin.MS93.S45A
public import CFSG.Quasithin.MS93.S46T

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Perfect

variable {𝔾 : Type} [Group 𝔾]

theorem commutator_mem_of_perfect {Lt D N : Subgroup 𝔾} (hperf : ⁅Lt, Lt⁆ = Lt) (hND : N ≤ D)
    (hDD : ⁅D, D⁆ ≤ N) (hDL : ⁅D, Lt⁆ ≤ N)
    {q : 𝔾} (hq : ∀ l ∈ Lt, ⁅q, l⁆ ∈ D) {l : 𝔾} (hl : l ∈ Lt) : ⁅q, l⁆ ∈ N := by
  have hNn : (N.subgroupOf D).Normal := ⟨fun n hn d => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 := hDD (Subgroup.commutator_mem_commutator d.2 (hND hn))
    have e : ((d * n * d⁻¹ : ↥D) : 𝔾) = ⁅(d : 𝔾), (n : 𝔾)⁆ * n := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]; group
    rw [e]
    exact N.mul_mem h1 hn⟩
  have hmk : ∀ x y : ↥D, (QuotientGroup.mk x : ↥D ⧸ N.subgroupOf D) = QuotientGroup.mk y ↔
      (x : 𝔾)⁻¹ * y ∈ N := fun x y => by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp
  have hcomm : ∀ x y : ↥D ⧸ N.subgroupOf D, x * y = y * x := by
    intro x y
    induction x using QuotientGroup.induction_on with | _ x => ?_
    induction y using QuotientGroup.induction_on with | _ y => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hmk]
    have h1 := hDD (Subgroup.commutator_mem_commutator (D.inv_mem y.2) (D.inv_mem x.2))
    have e : ((x * y : ↥D) : 𝔾)⁻¹ * ((y * x : ↥D) : 𝔾) = ⁅(y : 𝔾)⁻¹, (x : 𝔾)⁻¹⁆ := by
      simp only [Subgroup.coe_mul, commutatorElement_def]; group
    rw [e]
    exact h1
  let f : ↥Lt →* ↥D ⧸ N.subgroupOf D :=
    { toFun := fun l => QuotientGroup.mk ⟨⁅q, (l : 𝔾)⁆, hq l l.2⟩
      map_one' := by
        rw [← QuotientGroup.mk_one, hmk]
        simp [commutatorElement_def]
      map_mul' := fun l l' => by
        rw [← QuotientGroup.mk_mul, hmk]
        simp only [Subgroup.coe_mul]
        rw [S46.commutatorElement_mul_right_conj]
        have h1 : ⁅(l : 𝔾), ⁅q, (l' : 𝔾)⁆⁻¹⁆ ∈ N := by
          have h2 := Subgroup.commutator_mem_commutator l.2 (D.inv_mem (hq l' l'.2))
          rw [Subgroup.commutator_comm] at h2
          exact hDL h2
        have e : (⁅q, (l : 𝔾)⁆ * ((l : 𝔾) * ⁅q, (l' : 𝔾)⁆ * (l : 𝔾)⁻¹))⁻¹ *
            (⁅q, (l : 𝔾)⁆ * ⁅q, (l' : 𝔾)⁆) = ⁅(l : 𝔾), ⁅q, (l' : 𝔾)⁆⁻¹⁆ := by
          rw [commutatorElement_def (l : 𝔾)]; group
        rw [e]
        exact h1 }
  have hf : ∀ l : ↥Lt, f l = QuotientGroup.mk ⟨⁅q, (l : 𝔾)⁆, hq l l.2⟩ := fun _ => rfl
  have hker : ⁅Lt, Lt⁆ ≤ (f.ker).map Lt.subtype := by
    rw [Subgroup.commutator_le]
    intro l₁ hl₁ l₂ hl₂
    refine ⟨⁅(⟨l₁, hl₁⟩ : ↥Lt), ⟨l₂, hl₂⟩⁆, MonoidHom.mem_ker.mpr ?_, rfl⟩
    rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact hcomm _ _
  rw [hperf] at hker
  obtain ⟨l', hl', rfl⟩ := hker hl
  have hl'' := MonoidHom.mem_ker.mp hl'
  rw [hf, ← QuotientGroup.mk_one, hmk] at hl''
  simp only [Subgroup.coe_one, mul_one, inv_mem_iff] at hl''
  exact hl''

end Perfect

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

theorem exists_ltil_toSL3_eq {δ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ)
    {ψ : ↥(stab (puAmalgam c.hyp.le) δ) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab _ δ) (Uloc c.hyp.le L δ) ⊥ ψ false 1) (g : SL3 F) :
    ∃ l : ↥(stab (puAmalgam c.hyp.le) δ), (l : (puAmalgam c.hyp.le).Universal) ∈
      Ltil c.hyp.le L δ ∧ toSL3 ψ l = g := by
  have h := c.hyp
  obtain ⟨k, rfl⟩ := toSL3_surjective hψs g
  have hk : (k : (puAmalgam h.le).Universal) ∈ Ltil h.le L δ ⊔ Qv _ δ := by
    rw [← stab_eq_ltil_sup_qv h c.full hδ]; exact k.2
  have hLn : Ltil h.le L δ ≤ Subgroup.normalizer (Qv (puAmalgam h.le) δ : Set _) :=
    (ltil_le_stab h δ).trans (stab_le_normalizer_qv _ δ)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLn] at hk
  obtain ⟨l, hl, q, hq, hlq⟩ := hk
  have hls : l ∈ stab (puAmalgam h.le) δ := ltil_le_stab h δ hl
  have hqs : q ∈ stab (puAmalgam h.le) δ := qv_le_stab _ δ hq
  refine ⟨⟨l, hls⟩, hl, ?_⟩
  have hq1 : toSL3 ψ ⟨q, hqs⟩ = 1 := by
    have : (⟨q, hqs⟩ : ↥(stab (puAmalgam h.le) δ)) ∈ (toSL3 ψ).ker := by
      rw [c.ker_toSL3_eq hδ hψ, Subgroup.mem_subgroupOf]; exact hq
    exact this
  have e : k = ⟨l, hls⟩ * ⟨q, hqs⟩ := Subtype.ext hlq.symm
  rw [e, map_mul, hq1, mul_one]

theorem commutator_uloc_ltil {δ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ) :
    ⁅Uloc c.hyp.le L δ, Ltil c.hyp.le L δ⁆ = Uloc c.hyp.le L δ := by
  have h := c.hyp
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h c.via hδ
  have hLs := ltil_le_stab h δ
  have hle : ⁅Uloc h.le L δ, Ltil h.le L δ⁆ ≤ Uloc h.le L δ :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hLs.trans hψ.1)
  refine le_antisymm hle ?_
  obtain ⟨l, hl, hlg⟩ := c.exists_ltil_toSL3_eq hδ hψs hψ (rootElt 0 1 1)
  obtain ⟨u, hu⟩ := natVec_surjective hψ ![0, 1, 0]
  have hlu : (l : (puAmalgam h.le).Universal) * u * (l : (puAmalgam h.le).Universal)⁻¹ ∈
      Uloc h.le L δ := (Subgroup.mem_normalizer_iff.mp (hψ.1 l.2) _).mp u.2
  have hne : ⁅(u : (puAmalgam h.le).Universal), (l : (puAmalgam h.le).Universal)⁆ ≠ 1 := by
    intro h1
    rw [commutatorElement_eq_one_iff_commute] at h1
    have e1 : (⟨_, hlu⟩ : ↥(Uloc h.le L δ)) = u := by
      apply Subtype.ext
      show (l : (puAmalgam h.le).Universal) * u * (l : (puAmalgam h.le).Universal)⁻¹ = u
      rw [← h1.eq, mul_inv_cancel_right]
    have e2 := natVec_conj hψ l u ⟨_, hlu⟩ rfl
    rw [e1, hlg, hu, coe_rootElt (by decide)] at e2
    have := congrFun e2 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.single_apply,
      Matrix.one_apply] at this
  have hcU := hle (Subgroup.commutator_mem_commutator u.2 hl)
  refine (NatSec.ofIsSum hψ).le_of_invariant hψs (fun k x hx => ?_)
    (Subgroup.commutator_mem_commutator u.2 hl) hcU hne
  have hn : stab (puAmalgam h.le) δ ≤
      Subgroup.normalizer ((⁅Uloc h.le L δ, Ltil h.le L δ⁆ : Subgroup _) :
        Set (puAmalgam h.le).Universal) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ g ∈ stab (puAmalgam h.le) δ,
        ⁅Uloc h.le L δ, Ltil h.le L δ⁆.map (MulAut.conj g).toMonoidHom ≤
          ⁅Uloc h.le L δ, Ltil h.le L δ⁆ := by
      intro g hg
      rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer (hψ.1 hg),
        map_conj_eq_of_mem_normalizer (stab_le_normalizer_ltil h δ hg)]
    intro y
    constructor
    · intro hy; exact key g hg ⟨y, hy, rfl⟩
    · intro hy
      have := key g⁻¹ (inv_mem hg) ⟨_, hy, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using this
  exact (Subgroup.mem_normalizer_iff.mp (hn k.2) x).mp hx

theorem sup_inf_eq_of_dual {δ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ)
    {ψ : ↥(stab (puAmalgam c.hyp.le) δ) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab _ δ) (Uloc c.hyp.le L δ) ⊥ ψ false 1)
    {V W Z : Subgroup (puAmalgam c.hyp.le).Universal}
    (hd : IsSumOfNaturalModulesVia (stab _ δ) W Z ψ true 1)
    (hVn : stab (puAmalgam c.hyp.le) δ ≤ Subgroup.normalizer (V : Set _))
    (hWL : ⁅W, Ltil c.hyp.le L δ⁆ ≤ V) : (V ⊓ W) ⊔ Z = W := by
  have h := c.hyp
  set Nn := NatSec.ofIsSum hd with hNn
  refine le_antisymm (sup_le inf_le_right hd.2.1) ?_
  obtain ⟨x, hx, hxc⟩ := Nn.exists_coord_eq ![1, 0, 0]
  have hxZ : x ∉ Z := fun hxZ => by
    have := (Nn.coord_eq_zero_iff hx).mpr hxZ
    rw [hxc] at this
    have h0 := congrFun this 0
    simp at h0
  obtain ⟨l, hl, hlx⟩ : ∃ l ∈ Ltil h.le L δ, ⁅x, l⁆ ∉ Z := by
    by_contra hcon
    push Not at hcon
    exact hxZ (S46.mem_z_of_forall_commutator_mem hd (fun g => by
      obtain ⟨l, hl, hlg⟩ := c.exists_ltil_toSL3_eq hδ hψs hψ g
      exact ⟨l, hl, hlg⟩) hx hcon)
  have hlW : ⁅x, l⁆ ∈ W := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (hd.1 (ltil_le_stab h δ hl)) _).mp
      (W.inv_mem hx)
    have e : ⁅x, l⁆ = x * (l * x⁻¹ * l⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact W.mul_mem hx h1
  intro w hw
  obtain ⟨y, hy, -, hyw⟩ := Nn.exists_inv_mul_mem_of_invariant hψs
    (fun k y hy => Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_normalizer_iff.mp (hVn k.2) y).mp (Subgroup.mem_inf.mp hy).1,
        (Subgroup.mem_normalizer_iff.mp (hd.1 k.2) y).mp (Subgroup.mem_inf.mp hy).2⟩)
    (Subgroup.mem_inf.mpr ⟨hWL (Subgroup.commutator_mem_commutator hx hl), hlW⟩) hlW hlx hw
  have e : w = y * (y⁻¹ * w) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hyw)

end Ctx

end CFSG.Quasithin.MS93.S45
