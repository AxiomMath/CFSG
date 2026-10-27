module

public import CFSG.Quasithin.Vol2.Ch9Sec3Sp4Pt
public import CFSG.Quasithin.Vol2.Ch9Sec3Sp4Ln
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherMaximal
public import CFSG.Quasithin.Vol2.F134LieSp4Borel

public section

namespace CFSG.Quasithin.H13.Ch9.Sp4B

open Matrix CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open scoped MatrixGroups

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

@[expose] def fixSp (P : Subgroup (GL V₄ K)) : Submodule K (V₄ → K) where
  carrier := {v | ∀ g ∈ P, (g : Matrix V₄ V₄ K) *ᵥ v = v}
  add_mem' := fun {a b} ha hb g hg => by rw [mulVec_add, ha g hg, hb g hg]
  zero_mem' := fun g _ => mulVec_zero _
  smul_mem' := fun c {a} ha g hg => by rw [mulVec_smul, ha g hg]

@[expose] noncomputable def restrRep (P : Subgroup (GL V₄ K)) (C : Submodule K (V₄ → K))
    (hC : CFSG.RankThree.SubgroupLists.IsInvariant P C) : ↥P →* Module.End K ↥C where
  toFun g := (Matrix.mulVecLin ((g : GL V₄ K) : Matrix V₄ V₄ K)).restrict
    (fun v hv => hC g g.2 v hv)
  map_one' := LinearMap.ext fun v => Subtype.ext (by simp)
  map_mul' g h := LinearMap.ext fun v => Subtype.ext (by
    change (((g * h : ↥P) : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ (v : V₄ → K) =
      ((g : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ (((h : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ (v : V₄ → K))
    rw [Subgroup.coe_mul, Units.val_mul, mulVec_mulVec])

theorem fixSp_eq_top [Finite K] [CharP K 2] {P : Subgroup (GL V₄ K)} (hPS : P ≤ StatedSp 2 K)
    (hP2 : IsPGroup 2 P) (hR : fixSp P ⊓ orth (fixSp P) = ⊥) : fixSp P = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPA : CFSG.RankThree.SubgroupLists.IsInvariant P (fixSp P) :=
    fun g hg v hv => by rw [hv g hg]; exact hv
  have hPO : CFSG.RankThree.SubgroupLists.IsInvariant P (orth (fixSp P)) := isInvariant_orth hPS hPA
  have hC : orth (fixSp P) = ⊥ := by
    by_contra hC
    have : Nontrivial ↥(orth (fixSp P)) := Submodule.nontrivial_iff_ne_bot.mpr hC
    obtain ⟨c, hc0, hc⟩ := CFSG.LieType.BorelTits.exists_fixed_ne_zero
      (restrRep P (orth (fixSp P)) hPO) 2 ⊤ (hP2.of_equiv Subgroup.topEquiv.symm)
    have hcA : (c : V₄ → K) ∈ fixSp P := fun g hg =>
      congrArg Subtype.val (hc ⟨g, hg⟩ (Subgroup.mem_top _))
    have hcR : (c : V₄ → K) ∈ fixSp P ⊓ orth (fixSp P) := ⟨hcA, c.2⟩
    rw [hR, Submodule.mem_bot] at hcR
    exact hc0 (Subtype.ext hcR)
  have h := sup_orth_eq_top hR
  rwa [hC, sup_bot_eq] at h

structure Cfg (Lb Wb : Subgroup (GL V₄ K)) : Prop where
  hLS : Lb ≤ StatedSp 2 K
  hWS : Wb ≤ StatedSp 2 K
  perf : ⁅Lb, Lb⁆ = Lb
  h60 : ∀ N : Subgroup (GL V₄ K), N ≤ Lb → Lb ≤ Subgroup.normalizer (N : Set (GL V₄ K)) →
    IsPGroup 2 N → 60 ≤ N.relIndex Lb
  hW2 : IsPGroup 2 Wb
  hW16 : Nat.card Wb ≤ 16
  hLW : Lb ≤ Subgroup.normalizer (Wb : Set (GL V₄ K))

theorem Cfg.map_conj {Lb Wb : Subgroup (GL V₄ K)} (h : Cfg Lb Wb) {x : GL V₄ K}
    (hx : x ∈ StatedSp 2 K) :
    Cfg (Lb.map (MulAut.conj x).toMonoidHom) (Wb.map (MulAut.conj x).toMonoidHom) := by
  set φ := (MulAut.conj x).toMonoidHom with hφ
  have hinj : Function.Injective φ := (MulAut.conj x).injective
  have hsurj : Function.Surjective φ := (MulAut.conj x).surjective
  have hmapS : ∀ H : Subgroup (GL V₄ K), H ≤ StatedSp 2 K → H.map φ ≤ StatedSp 2 K := by
    rintro H hH _ ⟨y, hy, rfl⟩
    simp only [hφ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact mul_mem (mul_mem hx (hH hy)) (inv_mem hx)
  refine ⟨hmapS Lb h.hLS, hmapS Wb h.hWS, ?_, ?_, h.hW2.map φ, ?_, ?_⟩
  · rw [← Subgroup.map_commutator, h.perf]
  · intro N hNL hLN hN2
    set N₀ := N.comap φ with hN₀
    have hNN₀ : N₀.map φ = N := Subgroup.map_comap_eq_self_of_surjective hsurj N
    have hN₀L : N₀ ≤ Lb := by
      rw [hN₀, ← Subgroup.comap_map_eq_self_of_injective hinj Lb]
      exact Subgroup.comap_mono hNL
    have hLN₀ : Lb ≤ Subgroup.normalizer (N₀ : Set (GL V₄ K)) := by
      intro l hl
      rw [Subgroup.mem_normalizer_iff]
      intro y
      simp only [hN₀, Subgroup.mem_comap, map_mul, map_inv]
      exact Subgroup.mem_normalizer_iff.mp (hLN ⟨l, hl, rfl⟩) (φ y)
    have h60 := h.h60 N₀ hN₀L hLN₀ (hN2.comap_of_injective φ hinj)
    rw [← hNN₀, Subgroup.relIndex_map_map_of_injective N₀ Lb hinj]
    exact h60
  · rw [Subgroup.card_map_of_injective hinj]
    exact h.hW16
  · rw [hφ, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono h.hLW

theorem commute_of_cfg [Fintype K] (hK : Fintype.card K = 4) {Lb Wb : Subgroup (GL V₄ K)}
    (h : Cfg Lb Wb) : ∀ w ∈ Wb, ∀ l ∈ Lb, w * l = l * w := by
  have := charP_two_of_card_four hK
  set A₀ := fixSp Wb with hA₀
  set R := A₀ ⊓ orth A₀ with hR
  have hA₀L : CFSG.RankThree.SubgroupLists.IsInvariant Lb A₀ := by
    intro l hl v hv w hw
    have hw' : (l : GL V₄ K)⁻¹ * w * l ∈ Wb := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem (h.hLW hl)) w).mp hw
      rwa [inv_inv] at this
    rw [← gl_mulVec_mul, show w * (l : GL V₄ K) = l * ((l : GL V₄ K)⁻¹ * w * l) by group,
      gl_mulVec_mul, hv _ hw']
  have hOL : CFSG.RankThree.SubgroupLists.IsInvariant Lb (orth A₀) :=
    isInvariant_orth h.hLS hA₀L
  have hRL : CFSG.RankThree.SubgroupLists.IsInvariant Lb R :=
    fun l hl v hv => ⟨hA₀L l hl v hv.1, hOL l hl v hv.2⟩
  by_cases hR0 : R = ⊥
  ·
    have htop := fixSp_eq_top h.hWS h.hW2 hR0
    intro w hw l hl
    have hw1 : w = 1 := gl_ext_mulVec fun v => by
      rw [Units.val_one, one_mulVec]
      have hv : v ∈ A₀ := by
        rw [hA₀, htop]
        exact Submodule.mem_top
      exact hv w hw
    rw [hw1, one_mul, mul_one]
  have hRti : IsTotallyIsotropic (pairedSympForm K 2) R := fun x hx y hy =>
    (mem_orth.mp hy.2) x hx.1
  obtain ⟨d, g, hd1, hd2, hgR⟩ :=
    SymplecticHigher.exists_map_flag_eq_of_isTotallyIsotropic hR0 hRti
  set g' : GL V₄ K := (g : GL V₄ K) with hg'
  have hgS : g' ∈ StatedSp 2 K := g.2
  have hgF : ∀ u ∈ flag 2 K d, (g' : Matrix V₄ V₄ K) *ᵥ u ∈ R := fun u hu => by
    rw [← hgR]
    exact ⟨u, hu, rfl⟩
  have hgF' : ∀ v ∈ R, ((g'⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ v ∈ flag 2 K d := by
    intro v hv
    rw [← hgR] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    rw [SymplecticHigher.spAct, mulVecLin_apply, gl_inv_mulVec_mulVec]
    exact hu
  set φ := (MulAut.conj g'⁻¹).toMonoidHom with hφ
  have h' := h.map_conj (inv_mem hgS)
  have hφapp : ∀ y : GL V₄ K, φ y = g'⁻¹ * y * g' := fun y => by
    simp [hφ]
  have hLF : ∀ l' ∈ Lb.map φ, ∀ u ∈ flag 2 K d, (l' : Matrix V₄ V₄ K) *ᵥ u ∈ flag 2 K d := by
    rintro _ ⟨l, hl, rfl⟩ u hu
    rw [hφapp, gl_mulVec_mul, gl_mulVec_mul]
    exact hgF' _ (hRL l hl _ (hgF u hu))
  have hWF : ∀ w' ∈ Wb.map φ, ∀ u ∈ flag 2 K d, (w' : Matrix V₄ V₄ K) *ᵥ u = u := by
    rintro _ ⟨w, hw, rfl⟩ u hu
    rw [hφapp, gl_mulVec_mul, gl_mulVec_mul, (hgF u hu).1 w hw, gl_inv_mulVec_mulVec]
  have hcomm : ∀ w' ∈ Wb.map φ, ∀ l' ∈ Lb.map φ, w' * l' = l' * w' := by
    have hd : d = 1 ∨ d = 2 := by omega
    rcases hd with rfl | rfl
    · have he : (spE : V₄ → K) ∈ flag 2 K 1 :=
        F134.Sp4.mem_flag_one_iff.mpr ⟨by simp [spE], by simp [spE], by simp [spE]⟩
      refine commute_of_fix_spE hK h'.hLS h'.hWS h'.perf h'.h60 h'.hW2 h'.hW16 h'.hLW
        (fun l' hl' => ⟨_, F134.Sp4.eq_smul_e1_of_mem_flag_one (hLF l' hl' spE he)⟩)
        (fun w' hw' => hWF w' hw' spE he)
    · have hlag : ∀ v : V₄ → K, v ∈ lagInl ↔ v ∈ flag 2 K 2 := fun v => by
        rw [mem_lagInl, F134.Sp4.mem_flag_two_iff]
        exact ⟨fun hv => ⟨hv 0, hv 1⟩, fun hv i => by fin_cases i; exacts [hv.1, hv.2]⟩
      refine commute_of_fix_lagInl hK h'.hLS h'.hWS h'.perf h'.h60 h'.hW16 h'.hLW
        (fun l' hl' v hv => (hlag _).mpr (hLF l' hl' v ((hlag v).mp hv)))
        (fun w' hw' v hv => hWF w' hw' v ((hlag v).mp hv))
  intro w hw l hl
  have hc := hcomm _ ⟨w, hw, rfl⟩ _ ⟨l, hl, rfl⟩
  rw [← map_mul, ← map_mul] at hc
  exact (MulAut.conj g'⁻¹).injective hc

end CFSG.Quasithin.H13.Ch9.Sp4B
