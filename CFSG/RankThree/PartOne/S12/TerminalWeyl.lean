module

public import CFSG.RankThree.PartOne.S12.LAFaithful
public import CFSG.RankThree.PartOne.S12.TerminalWeylLA
import CFSG.RankThree.PartOne.S12.Sec127
import CFSG.RankThree.PartOne.LIT.KF126

public section

namespace CFSG.RankThree.PartOne

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

@[expose] def torusReflections (p : ℕ) (E : Subgroup G) : Set (MulAut E) :=
  {t | t ∈ torusWeyl E ∧ IsAutReflection p E t}

namespace TerminalW

open Equiv

section Transport

variable {E : Subgroup G} {n : ℕ} (f : Multiplicative (Fin n → ZMod 5) ≃* E)

omit [Finite G] in
theorem isRefl_iff (t : MulAut E) :
    TerminalLA.IsRefl (LinAlg.coordHom f t) ↔ IsAutReflection 5 E t :=
  (LinAlg.isAutReflection_iff f t).symm

omit [Finite G] in
theorem image_torusReflections :
    (LinAlg.coordHom f) '' torusReflections 5 E =
      TerminalLA.reflSet ((torusWeyl E).map (LinAlg.coordHom f)) := by
  ext t'
  constructor
  · rintro ⟨t, ⟨htW, htR⟩, rfl⟩
    exact ⟨Subgroup.mem_map_of_mem _ htW, (isRefl_iff f t).mpr htR⟩
  · rintro ⟨ht'Γ, ht'R⟩
    obtain ⟨t, htW, rfl⟩ := Subgroup.mem_map.mp ht'Γ
    exact ⟨t, ⟨htW, (isRefl_iff f t).mp ht'R⟩, rfl⟩

end Transport

end TerminalW

theorem terminal_weyl_structure (hD : ExtDickson) (hB : ExtBloomPrime) (hJP : ExtJonesParshall)
    {c : G} {L E B : Subgroup G} (hEel : IsElementaryAbelian 5 E) (hEcard : Nat.card E = 5 ^ 4)
    (hBE : B ≤ E) (hBcard : Nat.card B = 5 ^ 3) (hBinv : torusInvariant E ⊤ B)
    (hsup : E = Subgroup.zpowers c ⊔ B) (hinf : Subgroup.zpowers c ⊓ B = ⊥)
    (hcore : CFSG.pCore 5 ↥(torusWeyl E) = ⊥)
    (hirr : ∀ B' : Subgroup G, B' ≤ B → torusInvariant E ⊤ B' → B' = ⊥ ∨ B' = B)
    (hno : ∀ C : Subgroup G, C ≤ E → torusInvariant E ⊤ C → C ⊓ B = ⊥ → C ⊔ B = E → False)
    (hL : Nonempty (torusImage E L ≃* Equiv.Perm (Fin 4)))
    (hLgen : torusImage E L =
      Subgroup.closure {t | t ∈ torusImage E L ∧ IsAutReflection 5 E t})
    (_hLc : ∀ x ∈ L, c * x = x * c) :
    (∀ g ∈ torusWeyl E, (∀ b : E, (b : G) ∈ B → g b = b) → g = 1) ∧
    ∃ ψ : ↥(Subgroup.closure (torusReflections 5 E)) ≃* Equiv.Perm (Fin 5),
      (∀ (t : MulAut E) (ht : t ∈ torusReflections 5 E),
        (ψ ⟨t, Subgroup.subset_closure ht⟩).IsSwap) ∧
      (∀ σ : Equiv.Perm (Fin 5), σ.IsSwap →
        ∃ (t : MulAut E) (ht : t ∈ torusReflections 5 E),
          ψ ⟨t, Subgroup.subset_closure ht⟩ = σ) ∧
      (∀ e : E, (∀ t ∈ torusReflections 5 E, t e = e) → e = 1) ∧
      ∃ k : Fin 5, ∀ x ∈ torusImage E L,
        ∃ h : x ∈ Subgroup.closure (torusReflections 5 E), (ψ ⟨x, h⟩) k = k := by
  classical
  obtain ⟨f⟩ := LinAlg.exists_coords (p := 5) E hEcard
  have hcE : c ∈ E := by
    rw [hsup]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  have hczE : Subgroup.zpowers c ≤ E := Subgroup.zpowers_le.mpr hcE
  have hc1 : c ≠ 1 := by
    intro hc
    have h1 : E = B := by
      rw [hsup, hc, Subgroup.zpowers_one_eq_bot, bot_sup_eq]
    rw [h1, hBcard] at hEcard
    exact absurd (Nat.pow_right_injective (by norm_num : 2 ≤ 5) hEcard) (by norm_num)
  obtain ⟨v, hv⟩ := Sec127.exists_vec f hcE
  have hv0 : v ≠ 0 := Sec127.vec_ne_zero f hc1 hv
  have hdim : Module.finrank (ZMod 5) (LinAlg.bsub f B) + 1 = 4 :=
    Sec127.finrank_bsub_add_one f hv hv0 hczE hBE hsup hinf
  have hVdim : Module.finrank (ZMod 5) (Fin 4 → ZMod 5) = 4 := Module.finrank_fin_fun _
  have hdimV : Module.finrank (ZMod 5) (LinAlg.bsub f B) + 1 =
      Module.finrank (ZMod 5) (Fin 4 → ZMod 5) := by rw [hVdim]; exact hdim
  have hU3 : Module.finrank (ZMod 5) (LinAlg.bsub f B) = 3 := by omega
  have hUinv := Sec126g.invariant_bsub f hBE hBinv
  have hΓcore := Sec127.pCore_map_eq_bot f hcore
  have hnoline := Sec126g.no_invariant_line f hdim hBE hno
  have hfaith := laFaithful 5 (Fin 4 → ZMod 5) ((torusWeyl E).map (LinAlg.coordHom f))
    (LinAlg.bsub f B) hdimV hUinv hΓcore hnoline
  have hirrΓ : ∀ U' ≤ LinAlg.bsub f B,
      (∀ g ∈ (torusWeyl E).map (LinAlg.coordHom f), ∀ b ∈ U', g b ∈ U') →
      U' = ⊥ ∨ U' = LinAlg.bsub f B := by
    intro U' hU' hinv
    obtain ⟨C, hCE, rfl⟩ := LinAlg.exists_bsub_eq f U'
    have hCB : C ≤ B := (LinAlg.bsub_le_bsub_iff f hCE hBE).mp hU'
    have hCinv : torusInvariant E ⊤ C := by
      rw [LinAlg.torusInvariant_top_iff f hCE]
      intro φ hφ y hy
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
      exact hinv _ (Subgroup.mem_map_of_mem _ hφ) z hz
    rcases hirr C hCB hCinv with rfl | rfl
    · exact Or.inl (LinAlg.bsub_bot f)
    · exact Or.inr rfl
  obtain ⟨-, -, Y, hYΓ, hYn, hY60, -, hYperf, hYA5, hYcent⟩ := la126 hD hB hJP kf126 5
    (by norm_num) (Fin 4 → ZMod 5) ((torusWeyl E).map (LinAlg.coordHom f)) (LinAlg.bsub f B)
    hdimV (Or.inr hU3) hUinv hΓcore hfaith hirrΓ hnoline
  set Γ : Subgroup ((Fin 4 → ZMod 5) ≃ₗ[ZMod 5] (Fin 4 → ZMod 5)) :=
    (torusWeyl E).map (LinAlg.coordHom f) with hΓ
  have hTD : TerminalLA.TermData Γ Y (LinAlg.bsub f B) :=
    { dim := hdimV, dimU := hU3, inv := hUinv, faith := hfaith, irr := hirrΓ, noline := hnoline,
      YΓ := hYΓ, Yn := hYn, Yperf := hYperf, Ycent := hYcent }
  obtain ⟨e⟩ := hYA5
  set Λ : Subgroup ((Fin 4 → ZMod 5) ≃ₗ[ZMod 5] (Fin 4 → ZMod 5)) :=
    (torusImage E L).map (LinAlg.coordHom f) with hΛ
  have hΛΓ : Λ ≤ Γ := Subgroup.map_mono (Sec127.torusImage_le_torusWeyl E L)
  have hΛS4 : Nonempty (Λ ≃* Equiv.Perm (Fin 4)) :=
    ⟨(Subgroup.equivMapOfInjective (torusImage E L) (LinAlg.coordHom f)
      (LinAlg.coordHom_injective f)).symm.trans hL.some⟩
  have hΛgen : Λ = Subgroup.closure {t | t ∈ Λ ∧ TerminalLA.IsRefl t} := by
    have himg : (LinAlg.coordHom f) '' {t | t ∈ torusImage E L ∧ IsAutReflection 5 E t} =
        {t | t ∈ Λ ∧ TerminalLA.IsRefl t} := by
      ext t'
      constructor
      · rintro ⟨t, ⟨htL, htR⟩, rfl⟩
        exact ⟨Subgroup.mem_map_of_mem _ htL, (TerminalW.isRefl_iff f t).mpr htR⟩
      · rintro ⟨ht'Λ, ht'R⟩
        obtain ⟨t, htL, rfl⟩ := Subgroup.mem_map.mp ht'Λ
        exact ⟨t, ⟨htL, (TerminalW.isRefl_iff f t).mp ht'R⟩, rfl⟩
    rw [← himg, ← MonoidHom.map_closure, ← hLgen]
  obtain ⟨ψV, hψswap, hψsw, hψfix, k, hk⟩ :=
    TerminalLA.terminal_weyl_linear hTD e hΛΓ hΛS4 hΛgen
  set φ := LinAlg.coordHom f with hφ
  have hRimg : φ '' torusReflections 5 E = TerminalLA.reflSet Γ :=
    TerminalW.image_torusReflections f
  have hclos : (Subgroup.closure (torusReflections 5 E)).map φ =
      Subgroup.closure (TerminalLA.reflSet Γ) := by
    rw [MonoidHom.map_closure, hRimg]
  let ψE : ↥(Subgroup.closure (torusReflections 5 E)) ≃* Equiv.Perm (Fin 5) :=
    ((Subgroup.closure (torusReflections 5 E)).equivMapOfInjective φ
      (LinAlg.coordHom_injective f)).trans ((MulEquiv.subgroupCongr hclos).trans ψV)
  have hψE : ∀ (x : MulAut E) (hx : x ∈ Subgroup.closure (torusReflections 5 E))
      (hx' : φ x ∈ Subgroup.closure (TerminalLA.reflSet Γ)), ψE ⟨x, hx⟩ = ψV ⟨φ x, hx'⟩ :=
    fun x hx hx' => rfl
  refine ⟨?_, ψE, ?_, ?_, ?_, ?_⟩
  · intro g hg hgB
    apply LinAlg.coordHom_injective f
    rw [map_one]
    apply hfaith _ (Subgroup.mem_map_of_mem _ hg)
    intro b hb
    have hbB : ((f (Multiplicative.ofAdd b) : E) : G) ∈ B := (LinAlg.mem_bsub f B b).mp hb
    have h1 := hgB (f (Multiplicative.ofAdd b)) hbB
    rw [LinAlg.coordHom_apply, h1, MulEquiv.symm_apply_apply, toAdd_ofAdd]
  · intro t ht
    have hφt : φ t ∈ TerminalLA.reflSet Γ :=
      ⟨Subgroup.mem_map_of_mem _ ht.1, (TerminalW.isRefl_iff f t).mpr ht.2⟩
    rw [hψE t _ (Subgroup.subset_closure hφt)]
    exact hψswap (φ t) hφt
  · intro σ hσ
    obtain ⟨t', ht', hts⟩ := hψsw σ hσ
    have ht'' : t' ∈ φ '' torusReflections 5 E := by rw [hRimg]; exact ht'
    obtain ⟨t, htR, rfl⟩ := ht''
    exact ⟨t, htR, by rw [hψE t _ (Subgroup.subset_closure ht')]; exact hts⟩
  · intro e0 he0
    have hx : ∀ t' ∈ TerminalLA.reflSet Γ, t' (Multiplicative.toAdd (f.symm e0)) =
        Multiplicative.toAdd (f.symm e0) := by
      intro t' ht'
      rw [← hRimg] at ht'
      obtain ⟨t, htR, rfl⟩ := ht'
      rw [hφ, LinAlg.coordHom_apply, ofAdd_toAdd, MulEquiv.apply_symm_apply, he0 t htR]
    have h0 := hψfix _ hx
    have h1 : f.symm e0 = 1 := by
      have := congrArg Multiplicative.ofAdd h0
      simpa using this
    rw [← MulEquiv.apply_symm_apply f e0, h1, map_one]
  · refine ⟨k, fun x hxL => ?_⟩
    have hxΛ : φ x ∈ Λ := Subgroup.mem_map_of_mem _ hxL
    obtain ⟨h', hk'⟩ := hk (φ x) hxΛ
    have h'' : φ x ∈ (Subgroup.closure (torusReflections 5 E)).map φ := by
      rw [hclos]; exact h'
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h''
    have hyx' : y = x := LinAlg.coordHom_injective f hyx
    have hxin : x ∈ Subgroup.closure (torusReflections 5 E) := hyx' ▸ hy
    exact ⟨hxin, by rw [hψE x hxin h']; exact hk'⟩

end CFSG.RankThree.PartOne

