module

public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoOrth
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushCoreConj
public import CFSG.GroupTheory.CentralizerSup

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem relIndex_inf_centralizer_sup_conjSubgroup_le {Z A : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Z : Set G)) :
    (Z ⊓ Subgroup.centralizer ((A ⊔ conjSubgroup A g : Subgroup G) : Set G)).relIndex Z ≤
      ((Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z) ^ 2 := by
  have hg' : g⁻¹ ∈ Subgroup.normalizer (Z : Set G) := Subgroup.inv_mem _ hg
  simpa [CFSG.Quasithin.F53Push.cj, conjSubgroup] using
    CFSG.Quasithin.F53Push.relIndex_inf_centralizer_sup_cj_le
      (g := g⁻¹) (M := Z) (J := A) hg'

theorem str86_caseIIb_baum_inf_normal {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) {m : ℕ}
    (hCZ : S ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G) = Q2 L1 L2 S)
    {A : Subgroup G} (hA : IsMaxElemAbelian S A)
    (hZA : (Z2 L1 L2 S ⊓ Subgroup.centralizer (A : Set G)).relIndex (Z2 L1 L2 S) ≤ 2 ^ m)
    (heq : Nat.card (Z2 L1 L2 S) =
      (A ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G)).relIndex A *
        Nat.card (Z2 L1 L2 S ⊓ Subgroup.centralizer (A : Set G) : Subgroup G))
    {g : G} (hg : g ∈ u3H L1 L2 S) (hK : A ⊔ conjSubgroup A g ⊔ Q2 L1 L2 S = u3H L1 L2 S)
    (hZK : (2 ^ m) ^ 2 ≤ (Z2 L1 L2 S ⊓ Subgroup.centralizer
      ((A ⊔ conjSubgroup A g : Subgroup G) : Set G)).relIndex (Z2 L1 L2 S)) :
    P2 L1 L2 S ≤ Subgroup.normalizer ((baum S ⊓ Q2 L1 L2 S : Subgroup G) : Set G) := by
  classical
  set W : Subgroup G := omegaOneCenterOf (thompsonJ S) with hW
  set WM : Subgroup G := omegaOneCenterOf (thompsonJ (Q2 L1 L2 S)) with hWM
  set Astar : Subgroup G := (A ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G)) ⊔ Z2 L1 L2 S
    with hAstar
  have hZ2el : IsElemAbelian 2 (Z2 L1 L2 S) :=
    SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S)
  have hQ2S : Q2 L1 L2 S ≤ S := hCZ ▸ inf_le_left
  have hZ2Q2 : Z2 L1 L2 S ≤ Q2 L1 L2 S := omegaOneCenterOf_le (Q2 L1 L2 S)
  have hZ2S : Z2 L1 L2 S ≤ S := hZ2Q2.trans hQ2S
  have hQ2C : Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
    SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S)
  have hZ2cent : Z2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact CFSG.Open.IsElemAbelian.comm hZ2el hw hz
  have hB24 := B24_three hZ2el hZ2S hA heq
  have hAstarS : IsMaxElemAbelian S Astar := by
    simpa [hAstar] using hB24.1
  have hWWM : W ≤ WM := by
    have h := hB24.2.2.2.2
    simpa [hW, hWM, hCZ] using h
  have hZ2WM : Z2 L1 L2 S ≤ WM := by
    simpa [hWM] using
      C1Pack.omegaOneCenterOf_le_omegaOneCenterOf_thompsonJ (Q2 L1 L2 S)
  have hZ2leAstar : Z2 L1 L2 S ≤ Astar := by
    rw [hAstar]
    exact le_sup_right
  have hAstarQ2 : Astar ≤ Q2 L1 L2 S := by
    rw [hAstar, ← hCZ]
    exact sup_le (le_inf (inf_le_left.trans hA.1) inf_le_right) (le_inf hZ2S hZ2cent)
  have hAstarMaxQ2 : IsMaxElemAbelian (Q2 L1 L2 S) Astar :=
    ⟨hAstarQ2, hAstarS.2.1,
      fun B hB hBe => hAstarS.2.2 B (hB.trans hQ2S) hBe⟩
  have hWMleAstar : WM ≤ Astar := by
    simpa [hWM] using C56.omegaOneCenter_thompsonJ_le hAstarMaxQ2
  have hAA : A ≤ Subgroup.centralizer (A : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact CFSG.Open.IsElemAbelian.comm hA.2.1 hb ha
  have hH0C : A ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G) ≤
      Subgroup.centralizer (A : Set G) := inf_le_left.trans hAA
  set CW : Subgroup G := WM ⊓ Subgroup.centralizer (A : Set G) with hCW
  set CA : Subgroup G := Astar ⊓ Subgroup.centralizer (A : Set G) with hCA
  have hCW_eq : CW = CA ⊓ WM := by
    rw [hCW, hCA]
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hxW, hxC⟩
      exact ⟨⟨hWMleAstar hxW, hxC⟩, hxW⟩
    · rintro ⟨⟨-, hxC⟩, hxW⟩
      exact ⟨hxW, hxC⟩
  have hCW_bound1 : CW.relIndex WM ≤ CA.relIndex WM := by
    rw [hCW_eq]
    simpa [Subgroup.relIndex_self] using
      Subgroup.relIndex_inf_le (H := CA) (K := WM) (L := WM)
  have hCW_bound2 : CA.relIndex WM ≤ CA.relIndex Astar :=
    Subgroup.relIndex_le_of_le_right hWMleAstar Subgroup.index_ne_zero_of_finite
  have hH0_CA : A ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G) ≤ CA := by
    rw [hCA]
    exact le_inf (by rw [hAstar]; exact le_sup_left) hH0C
  have hAstar_eq_sup : Astar = Z2 L1 L2 S ⊔ CA := by
    refine le_antisymm ?_ ?_
    · rw [hAstar]
      exact sup_le (hH0_CA.trans le_sup_right) le_sup_left
    · rw [hCA]
      exact sup_le hZ2leAstar inf_le_left
  have hZ2_cent_CA : Z2 L1 L2 S ≤ Subgroup.centralizer (CA : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have hcA : c ∈ Astar := (Subgroup.mem_inf.mp (hCA ▸ hc)).1
    exact (CFSG.Open.IsElemAbelian.comm hAstarS.2.1 (hZ2leAstar hz) hcA).symm
  have hnorm_Z2_CA : Z2 L1 L2 S ≤ Subgroup.normalizer (CA : Set G) :=
    hZ2_cent_CA.trans (Subgroup.centralizer_le_normalizer _)
  have hsecond := CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
    (H := Z2 L1 L2 S) (K := CA) hnorm_Z2_CA
  have hCAZ : CA.relIndex Astar =
      (Z2 L1 L2 S ⊓ Subgroup.centralizer (A : Set G)).relIndex (Z2 L1 L2 S) := by
    rw [hAstar_eq_sup, hsecond.2]
    congr 1
    rw [hCA]
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hxZ, -, hxC⟩
      exact ⟨hxZ, hxC⟩
    · rintro ⟨hxZ, hxC⟩
      exact ⟨hxZ, hZ2leAstar hxZ, hxC⟩
  have hCWM_bound : CW.relIndex WM ≤ 2 ^ m :=
    hCW_bound1.trans (hCW_bound2.trans (hCAZ.trans_le hZA))
  have hgWM : g ∈ Subgroup.normalizer (WM : Set G) := by
    have hgP2 : g ∈ P2 L1 L2 S := (u3H_le_p2 L1 L2 S) hg
    have hgQ : g ∈ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
      (le_normalizer_pCoreOf 2 (P2 L1 L2 S)) hgP2
    have hgJ : g ∈ Subgroup.normalizer (thompsonJ (Q2 L1 L2 S) : Set G) :=
      (normalizer_le_normalizer_thompsonJ (Q2 L1 L2 S)) hgQ
    simpa [hWM] using
      (A4.normalizer_le_normalizer_omegaOneCenterOf (thompsonJ (Q2 L1 L2 S))) hgJ
  have hCWM_bound' : (WM ⊓ Subgroup.centralizer (A : Set G)).relIndex WM ≤ 2 ^ m := by
    simpa [hCW] using hCWM_bound
  have hb3 := relIndex_inf_centralizer_sup_conjSubgroup_le (Z := WM) (A := A) (g := g) hgWM
  have hWMK_bound : (WM ⊓ Subgroup.centralizer
      ((A ⊔ conjSubgroup A g : Subgroup G) : Set G)).relIndex WM ≤ (2 ^ m) ^ 2 :=
    hb3.trans (Nat.pow_le_pow_left hCWM_bound' 2)
  set C0 : Subgroup G := WM ⊓ Subgroup.centralizer
    ((A ⊔ conjSubgroup A g : Subgroup G) : Set G) with hC0
  have hWMel : IsElemAbelian 2 WM := by
    simpa [hWM] using SmithC27.isElemAbelian_omegaOneCenterOf (thompsonJ (Q2 L1 L2 S))
  have hWMK_bound' : C0.relIndex WM ≤ (2 ^ m) ^ 2 := by
    simpa [hC0] using hWMK_bound
  have hZ2_cent_C0 : Z2 L1 L2 S ≤ Subgroup.centralizer (C0 : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (CFSG.Open.IsElemAbelian.comm hWMel (hZ2WM hz)
      (Subgroup.mem_inf.mp (hC0 ▸ hc)).1).symm
  have hC0_cent_Z2 : C0 ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hcWM : c ∈ WM := (Subgroup.mem_inf.mp (hC0 ▸ hc)).1
    exact (CFSG.Open.IsElemAbelian.comm hWMel hcWM (hZ2WM hz)).symm
  have hC0_norm_Z2 : C0 ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    hC0_cent_Z2.trans (Subgroup.centralizer_le_normalizer _)
  have hnorm_Z2_C0 : Z2 L1 L2 S ≤ Subgroup.normalizer (C0 : Set G) :=
    hZ2_cent_C0.trans (Subgroup.centralizer_le_normalizer _)
  have hsecond0 := CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
    (H := Z2 L1 L2 S) (K := C0) hnorm_Z2_C0
  have hC0_sup_eq : C0.relIndex (Z2 L1 L2 S ⊔ C0) =
      (Z2 L1 L2 S ⊓ Subgroup.centralizer
        ((A ⊔ conjSubgroup A g : Subgroup G) : Set G)).relIndex (Z2 L1 L2 S) := by
    rw [hsecond0.2]
    congr 1
    rw [hC0]
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hxZ, -, hxC⟩
      exact ⟨hxZ, hxC⟩
    · rintro ⟨hxZ, hxC⟩
      exact ⟨hxZ, hZ2WM hxZ, hxC⟩
  have hC0_sup_ge : (2 ^ m) ^ 2 ≤ C0.relIndex (Z2 L1 L2 S ⊔ C0) := by
    rw [hC0_sup_eq]
    exact hZK
  have hprod : C0.relIndex (Z2 L1 L2 S ⊔ C0) * (Z2 L1 L2 S ⊔ C0).relIndex WM =
      C0.relIndex WM :=
    Subgroup.relIndex_mul_relIndex (H := C0) (K := Z2 L1 L2 S ⊔ C0) (L := WM)
      le_sup_right (by rw [hC0]; exact sup_le hZ2WM inf_le_left)
  have hpos : 0 < C0.relIndex (Z2 L1 L2 S ⊔ C0) :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hsup_rel : (Z2 L1 L2 S ⊔ C0).relIndex WM = 1 := by
    have h2 : C0.relIndex (Z2 L1 L2 S ⊔ C0) * (Z2 L1 L2 S ⊔ C0).relIndex WM ≤
        C0.relIndex (Z2 L1 L2 S ⊔ C0) * 1 := by
      calc
        C0.relIndex (Z2 L1 L2 S ⊔ C0) * (Z2 L1 L2 S ⊔ C0).relIndex WM
            = C0.relIndex WM := hprod
        _ ≤ (2 ^ m) ^ 2 := hWMK_bound'
        _ ≤ C0.relIndex (Z2 L1 L2 S ⊔ C0) := hC0_sup_ge
        _ = C0.relIndex (Z2 L1 L2 S ⊔ C0) * 1 := (mul_one _).symm
    exact le_antisymm (Nat.le_of_mul_le_mul_left h2 hpos)
      (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
  have hWM_eq : WM = Z2 L1 L2 S ⊔ C0 := by
    refine le_antisymm (Subgroup.relIndex_eq_one.mp hsup_rel) ?_
    exact sup_le hZ2WM (by rw [hC0]; exact inf_le_left)
  have hK_le_u3H : (A ⊔ conjSubgroup A g : Subgroup G) ≤ u3H L1 L2 S := by
    rw [← hK]
    exact le_sup_left
  have hK_le_p2 : (A ⊔ conjSubgroup A g : Subgroup G) ≤ P2 L1 L2 S :=
    hK_le_u3H.trans (u3H_le_p2 L1 L2 S)
  have hforward : ∀ x ∈ (A ⊔ conjSubgroup A g : Subgroup G),
      ∀ y ∈ (Z2 L1 L2 S ⊔ W : Subgroup G),
        x * y * x⁻¹ ∈ (Z2 L1 L2 S ⊔ W : Subgroup G) := by
    intro x hx y hy
    have hxU : x ∈ u3H L1 L2 S := hK_le_u3H hx
    have hxZ : x ∈ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
      str86_z2_normal_u3H L1 L2 S hxU
    have hcomap : (Z2 L1 L2 S ⊔ W : Subgroup G) ≤
        (Z2 L1 L2 S ⊔ W : Subgroup G).comap (MulAut.conj x).toMonoidHom := by
      refine sup_le ?_ ?_
      · intro z hz
        rw [Subgroup.mem_comap]
        change x * z * x⁻¹ ∈ Z2 L1 L2 S ⊔ W
        exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hxZ z).mp hz)
      · intro w hw
        rw [Subgroup.mem_comap]
        change x * w * x⁻¹ ∈ Z2 L1 L2 S ⊔ W
        have hwWM : w ∈ WM := hWWM hw
        rw [hWM_eq] at hwWM
        obtain ⟨z, hz, c, hc, rfl⟩ :=
          (F1.mem_sup_iff_exists_mul_of_normalizes hC0_norm_Z2).mp hwWM
        have hcx : x * c = c * x :=
          Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hC0 ▸ hc)).2 x hx
        have hxz : x * z * x⁻¹ ∈ Z2 L1 L2 S :=
          (Subgroup.mem_normalizer_iff.mp hxZ z).mp hz
        have hxz' : x * z * x⁻¹ * z⁻¹ ∈ Z2 L1 L2 S :=
          (Z2 L1 L2 S).mul_mem hxz ((Z2 L1 L2 S).inv_mem hz)
        have hxc : x * c * x⁻¹ = c := by
          calc x * c * x⁻¹ = c * x * x⁻¹ := by rw [hcx]
            _ = c := by group
        have hcx' : c * x⁻¹ = x⁻¹ * c := by
          calc c * x⁻¹ = x⁻¹ * (x * c) * x⁻¹ := by group
            _ = x⁻¹ * (c * x) * x⁻¹ := by rw [hcx]
            _ = x⁻¹ * c := by group
        have hval : x * (z * c) * x⁻¹ = (x * z * x⁻¹ * z⁻¹) * (z * c) := by
          calc x * (z * c) * x⁻¹ = x * z * (c * x⁻¹) := by group
            _ = x * z * (x⁻¹ * c) := by rw [hcx']
            _ = (x * z * x⁻¹) * c := by group
            _ = (x * z * x⁻¹ * z⁻¹) * (z * c) := by group
        rw [hval]
        exact (Z2 L1 L2 S ⊔ W : Subgroup G).mul_mem
          (Subgroup.mem_sup_left hxz') (Subgroup.mem_sup_right hw)
    have hmem : x * y * x⁻¹ ∈ (Z2 L1 L2 S ⊔ W : Subgroup G) := by
      have h' := Subgroup.mem_comap.mp (hcomap hy)
      change (MulAut.conj x) y ∈ (Z2 L1 L2 S ⊔ W : Subgroup G) at h'
      simpa only [MulAut.conj_apply] using h'
    exact hmem
  have hK_le_N_H : (A ⊔ conjSubgroup A g : Subgroup G) ≤
      Subgroup.normalizer ((Z2 L1 L2 S ⊔ W : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hforward x hx y
    · intro hy
      have h1 := hforward x⁻¹ ((A ⊔ conjSubgroup A g).inv_mem hx) (x * y * x⁻¹) hy
      have h1' : x⁻¹ * (x * y * x⁻¹) * (x⁻¹)⁻¹ = y := by group
      rwa [h1'] at h1
  have hR_eq : (baum S ⊓ Q2 L1 L2 S : Subgroup G) =
      Q2 L1 L2 S ⊓ Subgroup.centralizer ((Z2 L1 L2 S ⊔ W : Subgroup G) : Set G) := by
    rw [baum, hW, CFSG.centralizer_sup_eq]
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨hxS, hxW⟩, hxQ⟩
      exact ⟨hxQ, hQ2C hxQ, hxW⟩
    · rintro ⟨hxQ, -, hxW⟩
      exact ⟨⟨hQ2S hxQ, hxW⟩, hxQ⟩
  have hK_Q2norm : (A ⊔ conjSubgroup A g : Subgroup G) ≤
      Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    hK_le_p2.trans (le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  have hK_Cnorm : (A ⊔ conjSubgroup A g : Subgroup G) ≤ Subgroup.normalizer
      (Subgroup.centralizer ((Z2 L1 L2 S ⊔ W : Subgroup G) : Set G) : Set G) :=
    hK_le_N_H.trans (F7.normalizer_le_normalizer_centralizer (Z2 L1 L2 S ⊔ W))
  have hK_R : (A ⊔ conjSubgroup A g : Subgroup G) ≤
      Subgroup.normalizer ((baum S ⊓ Q2 L1 L2 S : Subgroup G) : Set G) := by
    rw [hR_eq]
    exact F7.le_normalizer_inf hK_Q2norm hK_Cnorm
  have hbigB_R : bigB L1 L2 S ≤
      Subgroup.normalizer ((baum S ⊓ Q2 L1 L2 S : Subgroup G) : Set G) := by
    have hbigB_P2 : bigB L1 L2 S ≤ P2 L1 L2 S := le_sup_right
    have hbigB_Q2 : bigB L1 L2 S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
      hbigB_P2.trans (le_normalizer_pCoreOf 2 (P2 L1 L2 S))
    have hbigB_W : bigB L1 L2 S ≤ Subgroup.normalizer (W : Set G) :=
      (hSB.trans (normalizer_le_normalizer_thompsonJ S)).trans
        (A4.normalizer_le_normalizer_omegaOneCenterOf (thompsonJ S))
    have hbigB_Z2 : bigB L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
      hbigB_P2.trans ((le_normalizer_pCoreOf 2 (P2 L1 L2 S)).trans
        (A4.normalizer_le_normalizer_omegaOneCenterOf (Q2 L1 L2 S)))
    have hbigB_CZ2 : bigB L1 L2 S ≤ Subgroup.normalizer
        (Subgroup.centralizer (Z2 L1 L2 S : Set G) : Set G) :=
      hbigB_Z2.trans (F7.normalizer_le_normalizer_centralizer (Z2 L1 L2 S))
    have hbigB_CW : bigB L1 L2 S ≤ Subgroup.normalizer
        (Subgroup.centralizer (W : Set G) : Set G) :=
      hbigB_W.trans (F7.normalizer_le_normalizer_centralizer W)
    rw [hR_eq, CFSG.centralizer_sup_eq]
    exact F7.le_normalizer_inf hbigB_Q2 (F7.le_normalizer_inf hbigB_CZ2 hbigB_CW)
  have hKsupB_R : (A ⊔ conjSubgroup A g) ⊔ bigB L1 L2 S ≤
      Subgroup.normalizer ((baum S ⊓ Q2 L1 L2 S : Subgroup G) : Set G) :=
    sup_le hK_R hbigB_R
  have hQ2B : Q2 L1 L2 S ≤ bigB L1 L2 S := hQ2S.trans le_sup_right
  have hL2_le : L2 ≤ (A ⊔ conjSubgroup A g) ⊔ bigB L1 L2 S := by
    refine (l2_le_u3H L1 L2 S).trans ?_
    rw [← hK]
    exact sup_le le_sup_left (hQ2B.trans le_sup_right)
  have hP2_le : P2 L1 L2 S ≤ (A ⊔ conjSubgroup A g) ⊔ bigB L1 L2 S :=
    sup_le hL2_le le_sup_right
  exact hP2_le.trans hKsupB_R

end CFSG.Quasithin.Stroth

end
