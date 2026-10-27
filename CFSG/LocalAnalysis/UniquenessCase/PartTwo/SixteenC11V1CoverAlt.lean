module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1Restrict
public import CFSG.Quasithin.H13.VolIAltCoverSeven
public import CFSG.CGT.PushingUpLit.SolK.PermModule
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitAltNatural

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

theorem s16c11_v1_cover_alt_seven : S16C11V1ModelCover (FFModel.altDn 7) := by
  intro W _ _ hW2 H Z hZ hcomm h
  exact CFSG.Quasithin.H13.VolI.altNaturalCoverSeven_holds W hW2 H Z hZ hcomm h

theorem s16c11_v1_cover_alt_odd {n : ℕ} (hn : Odd n) (h5 : 5 ≤ n) :
    S16C11V1ModelCover (FFModel.altDn n) := by
  intro W _ _ hW2 H Z hZ hcomm h
  by_cases hH : H = ⊥
  · subst hH
    have hbot : commV (⊥ : Subgroup (MulAut W)) = ⊥ := by
      rw [commV_eq_commSub, commSub_eq_bot_iff]
      intro w _ x hx
      rw [Subgroup.mem_bot] at hx
      rw [hx]
      rfl
    rw [hbot] at hcomm
    rw [eq_bot_iff]
    intro z _
    rw [hcomm]
    exact Subgroup.mem_top z
  · obtain ⟨π, hπs, -, -, -, -, hsec, hker, β₀, hβs, hβk, hβe⟩ := h
    haveI : IsSimpleGroup (FFModel.altDn n).Gam :=
      alternatingGroup.isSimpleGroup (by simpa using h5)
    have hπinj : Function.Injective π := by
      rw [← MonoidHom.ker_eq_bot_iff]
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h1 | h1
      · exact h1
      · exfalso
        apply hH
        rw [eq_bot_iff]
        intro x hx
        obtain ⟨γ, hγ⟩ := hπs ⟨x, hx⟩
        have h2 : γ ∈ π.ker := by rw [h1]; exact Subgroup.mem_top γ
        rw [MonoidHom.mem_ker] at h2
        rw [Subgroup.mem_bot]
        have hγ' : ((π γ : ↥H) : MulAut W) = x := congrArg Subtype.val hγ
        have h2' : ((π γ : ↥H) : MulAut W) = 1 := congrArg Subtype.val h2
        rw [← hγ']
        exact h2'
    let πe : (FFModel.altDn n).Gam ≃* ↥H := MulEquiv.ofBijective π ⟨hπinj, hπs⟩
    let θ : ↥H ≃* (FFModel.altDn n).Gam := πe.symm
    let θp : ↥H → Equiv.Perm (Fin n) :=
      fun e => Subtype.val (show ↥(alternatingGroup (Fin n)) from θ e)
    have hθπ : ∀ e : ↥H, π (θ e) = e := fun e => MulEquiv.apply_symm_apply πe e
    have hker_bot : (FFModel.altDn n).ker.subgroupOf (FFModel.altDn n).sec = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      rw [Subgroup.mem_subgroupOf] at hx
      apply Subtype.ext
      exact CFSG.Quasithin.H13.Orbit.altDn_ker_odd hn hx
    let ρ : (↥(FFModel.altDn n).sec ⧸
        (FFModel.altDn n).ker.subgroupOf (FFModel.altDn n).sec) ≃* ↥(FFModel.altDn n).sec :=
      (QuotientGroup.quotientMulEquivOfEq hker_bot).trans QuotientGroup.quotientBot
    have hρmk : ∀ q : ↥(FFModel.altDn n).sec ⧸
        (FFModel.altDn n).ker.subgroupOf (FFModel.altDn n).sec,
        QuotientGroup.mk (ρ q) = q := by
      intro q
      obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
      rfl
    have hρmk' : ∀ m : ↥(FFModel.altDn n).sec,
        ρ (QuotientGroup.mk m) = m := fun _ => rfl
    let β : W →* ↥(FFModel.altDn n).sec :=
      ρ.toMonoidHom.comp (β₀.comp ((Subgroup.topEquiv (G := W)).symm).toMonoidHom)
    have hβeq : ∀ w : W, β w = ρ (β₀ (Subgroup.topEquiv.symm w)) := fun _ => rfl
    have hβmult : ∀ u : ↥(⊤ : Subgroup W), β (u : W) = ρ (β₀ u) := by
      intro u
      have h := hβeq (Subgroup.topEquiv u)
      rw [MulEquiv.symm_apply_apply] at h
      exact h
    have hβsurj : Function.Surjective β := by
      intro x
      obtain ⟨u, hu⟩ := hβs (ρ.symm x)
      refine ⟨(u : W), ?_⟩
      rw [hβmult u, hu, MulEquiv.apply_symm_apply]
    have hβfix : ∀ w : W, β w = 1 → w ∈ fixV H := by
      intro w hw
      have h1 : β₀ (Subgroup.topEquiv.symm w) = 1 := by
        have h2 := congrArg ρ.symm hw
        rw [hβeq w, MulEquiv.symm_apply_apply, map_one] at h2
        exact h2
      have h3 : (Subgroup.topEquiv.symm w : W) ∈ Z := (hβk (Subgroup.topEquiv.symm w)).1 h1
      exact hZ h3
    have hβequivar : ∀ (e : ↥H) (w : W),
        β ((e : MulAut W) w) =
          G6.coreAct n (θp e) (show ↥(G6.coreMod n) from β w) := by
      intro e w
      let u : ↥(⊤ : Subgroup W) := Subgroup.topEquiv.symm w
      have hbu : β w = ρ (β₀ u) := rfl
      have hm : (FFModel.altDn n).act (θ e) (β w) ∈ (FFModel.altDn n).sec :=
        hsec (θ e) (β w) (β w).2
      have hbound : β₀ u = QuotientGroup.mk (β w) := by
        have h := hρmk (β₀ u)
        rw [← h]
        rfl
      have hkey := hβe (θ e) u (β w) (Subgroup.mem_top _) hm hbound
      have h2 : ρ (β₀ ⟨((π (θ e) : ↥H) : MulAut W) (u : W), Subgroup.mem_top _⟩)
          = ⟨(FFModel.altDn n).act (θ e) (β w), hm⟩ :=
        (congrArg ρ hkey).trans (hρmk' ⟨(FFModel.altDn n).act (θ e) (β w), hm⟩)
      have harg : (⟨((π (θ e) : ↥H) : MulAut W) (u : W),
            Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup W))
          = Subgroup.topEquiv.symm ((e : MulAut W) w) := by
        apply Subtype.ext
        show ((π (θ e) : ↥H) : MulAut W) (u : W) = ((e : MulAut W) w : W)
        have hcoe : ((π (θ e) : ↥H) : MulAut W) = (e : MulAut W) :=
          congrArg Subtype.val (hθπ e)
        rw [hcoe]
        rfl
      have hL : ρ (β₀ ⟨((π (θ e) : ↥H) : MulAut W) (u : W), Subgroup.mem_top _⟩)
          = β ((e : MulAut W) w) := by
        rw [harg]
        rfl
      rw [hL] at h2
      rw [h2]
      apply Subtype.ext
      rw [G6.coreAct_coe]
      rfl
    let D : CFSG.CGT.PushingUpLit.BHS.AltNatData H n :=
      ⟨θ, β, hβsurj, hβfix, hβequivar, hcomm⟩
    have hfix : fixV H = ⊥ :=
      CFSG.CGT.PushingUpLit.SolK.altNatData_fixV_eq_bot hW2 hn h5 D
    rw [hfix] at hZ
    exact le_bot_iff.mp hZ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
