module

public import CFSG.Monster.GMS.ASegAmalgamTheta
public import CFSG.Monster.GMS.ASegTitsTri
public import Certificates.Certificate3015
public import Certificates.Certificate3016
public import Certificates.Certificate3017
public import Certificates.Certificate3018
public import Certificates.Certificate3019
public import Certificates.Certificate3020
public import Certificates.Certificate3021
public import Certificates.Certificate3024
public import Certificates.Certificate10032
public import Certificates.Certificate10033
public import Certificates.Certificate10034
public import Certificates.Certificate10035
public import Certificates.Certificate10042
public import Certificates.Certificate10043
public import Certificates.Certificate10044
public import Certificates.Certificate10045
public import Certificates.Certificate10069
public import Certificates.Certificate10070
public import Certificates.Certificate10072
public import Certificates.Certificate10073
public import Certificates.Certificate10074
public import Certificates.Certificate10075
public import Certificates.Certificate10076
public import Certificates.Certificate8955

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic CFSG.Monster.B.Recog CFSG.Monster.GMS.S4Assembly
  CFSG.Monster.GMS.S4Family

local notation "C[" x "]" => Subgroup.centralizer ({x} : Set _)

section EdgeGroup

variable {G : Type} [Group G] {d₀ : B} {a z₀ y z : G}

theorem K_le_edgeStab (D : ASegData a z₀ y z) :
    C[a] ⊓ C[y] ≤ edgeStab (vertA a) (vertY D) := fun _ hk =>
  (mem_edgeStab_iff D).2 (Or.inl ⟨conj_eq_of_mem_centralizer hk.1, conj_eq_of_mem_centralizer hk.2⟩)

theorem edgeStab_le_Xt0 [Finite G] (D : ASegData a z₀ y z) (h : Comm3 a y z) :
    edgeStab (vertA a) (vertY D) ≤ Xt0 a y := fun _ hg =>
  mem_Xt0_of_fix_or_swap h ((mem_edgeStab_iff D).1 hg)

theorem edgeStab_inf_le_Xt1 [Finite G] (D : ASegData a z₀ y z) (h : Comm3 a y z) :
    edgeStab (vertA a) (vertY D) ⊓ C[z] ≤ Xt1 a y z := by
  intro g hg
  refine ⟨hg.2, ?_⟩
  have e : g * (a * y * z) * g⁻¹ = (g * a * g⁻¹) * (g * y * g⁻¹) * (g * z * g⁻¹) := by group
  have hgz := conj_eq_of_mem_centralizer hg.2
  rcases (mem_edgeStab_iff D).1 hg.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine mem_normalizer_triple ?_ ?_ ?_
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; exact Or.inr (Or.inl rfl)
    · rw [e, h1, h2, hgz]; exact Or.inr (Or.inr rfl)
  · refine mem_normalizer_triple ?_ ?_ ?_
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; exact Or.inl rfl
    · rw [e, h1, h2, hgz, show y * a * z = a * y * z by comm3_simp h]; exact Or.inr (Or.inr rfl)

end EdgeGroup

section Assemble

variable {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G'] {d₀ d₀' : B}
  {a z₀ y z : G} {a' z₀' y' z' : G'} {A Z : G → G'}

structure AmalgamIsos (a y z : G) (a' y' z' : G') (D : ASegData a z₀ y z)
    (D' : ASegData a' z₀' y' z') (A Z : G → G') : Prop where
  hv : IsIsoOn A C[a] C[a']
  he : IsIsoOn (asegTheta A Z a y z) (edgeStab (vertA a) (vertY D))
    (edgeStab (vertA a') (vertY D'))
  ht : ∀ j, IsIsoOn (cond j Z (asegTheta A Z a y z)) (XtB a y z j) (XtB a' y' z' j)
  hve : ∀ g ∈ C[a] ⊓ edgeStab (vertA a) (vertY D), A g = asegTheta A Z a y z g
  hvt : ∀ j, ∀ g ∈ C[a] ⊓ XtB a y z j, A g = cond j Z (asegTheta A Z a y z) g
  het : ∀ j, ∀ g ∈ edgeStab (vertA a) (vertY D) ⊓ XtB a y z j,
    asegTheta A Z a y z g = cond j Z (asegTheta A Z a y z) g
  hve' : ∀ g ∈ C[a], A g ∈ edgeStab (vertA a') (vertY D') → g ∈ edgeStab (vertA a) (vertY D)
  hvt' : ∀ j, ∀ g ∈ C[a], A g ∈ XtB a' y' z' j → g ∈ XtB a y z j
  het' : ∀ j, ∀ g ∈ edgeStab (vertA a) (vertY D),
    asegTheta A Z a y z g ∈ XtB a' y' z' j → g ∈ XtB a y z j

theorem amalgamIsos_of (hG : GMSF1Type d₀ a z₀) (D : ASegData a z₀ y z)
    (D' : ASegData a' z₀' y' z') (Q : AmalgamData a y z a' y' z' A Z) :
    AmalgamIsos a y z a' y' z' D D' A Z := by
  have P := Q.alphaZeta
  have h := Q.comm3
  have h' := Q.comm3'
  have hne : a ≠ y := D.a_ne_y hG
  have hθ : IsIsoOn (asegTheta A Z a y z) (Xt0 a y) (Xt0 a' y') := Q.isIsoOn_theta
  have haC : a ∈ C[a] := self_mem_centralizer a
  have hKA : ∀ k ∈ C[a] ⊓ C[y], A k ∈ C[a'] ⊓ C[y'] := fun k hk => Q.isIsoOn_K.map_mem k hk
  have hEA : ∀ g ∈ C[a], A g ∈ edgeStab (vertA a') (vertY D') ↔ g ∈ edgeStab (vertA a) (vertY D) :=
    fun g hg => by
      rw [mem_edgeStab_iff D', mem_edgeStab_iff D]
      have := fix_or_swap_iff_of_isIsoOn P.hA haC h.y_mem_cent_a hg
      rwa [P.A_a, P.A_y] at this
  have hEZ : ∀ w ∈ C[z], Z w ∈ edgeStab (vertA a') (vertY D') ↔ w ∈ edgeStab (vertA a) (vertY D) :=
    fun w hw => by
      rw [mem_edgeStab_iff D', mem_edgeStab_iff D]
      have := fix_or_swap_iff_of_isIsoOn P.hZ h.a_mem_cent_z h.y_mem_cent_z hw
      rwa [P.Z_a, P.Z_y] at this
  have hθE : ∀ g ∈ Xt0 a y, asegTheta A Z a y z g ∈ edgeStab (vertA a') (vertY D') ↔
      g ∈ edgeStab (vertA a) (vertY D) := by
    intro g hg
    obtain ⟨k, hk, w, hw, rfl⟩ := Q.dec g hg
    rw [Q.theta_mul hk hw]
    have hAk : A k ∈ edgeStab (vertA a') (vertY D') := K_le_edgeStab D' (hKA k hk)
    have hk' : k ∈ edgeStab (vertA a) (vertY D) := K_le_edgeStab D hk
    constructor
    · intro hmem
      have : Z w ∈ edgeStab (vertA a') (vertY D') := by
        have := (edgeStab (vertA a') (vertY D')).mul_mem ((edgeStab (vertA a') (vertY D')).inv_mem
          hAk) hmem
        rwa [inv_mul_cancel_left] at this
      exact (edgeStab (vertA a) (vertY D)).mul_mem hk' ((hEZ w hw.2).1 this)
    · intro hmem
      have : w ∈ edgeStab (vertA a) (vertY D) := by
        have := (edgeStab (vertA a) (vertY D)).mul_mem ((edgeStab (vertA a) (vertY D)).inv_mem
          hk') hmem
        rwa [inv_mul_cancel_left] at this
      exact (edgeStab (vertA a') (vertY D')).mul_mem hAk ((hEZ w hw.2).2 this)
  have he : IsIsoOn (asegTheta A Z a y z) (edgeStab (vertA a) (vertY D))
      (edgeStab (vertA a') (vertY D')) :=
    hθ.restrict (edgeStab_le_Xt0 D h) (edgeStab_le_Xt0 D' h') hθE
  have hZ1 : IsIsoOn Z (Xt1 a y z) (Xt1 a' y' z') := by
    refine P.hZ.restrict (fun g hg => hg.1) (fun g hg => hg.1) (fun g hg => ?_)
    have := mem_Xt1_iff_of_isIsoOn P.hZ h.a_mem_cent_z h.y_mem_cent_z (self_mem_centralizer z) hg
    rwa [P.Z_a, P.Z_y, P.Z_z] at this
  have hve : ∀ g ∈ C[a] ⊓ edgeStab (vertA a) (vertY D), A g = asegTheta A Z a y z g := by
    intro g hg
    have hgK : g ∈ C[a] ⊓ C[y] := by
      refine ⟨hg.1, ?_⟩
      rcases (mem_edgeStab_iff D).1 hg.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact mem_centralizer_of_conj_eq h2
      · exact absurd ((conj_eq_of_mem_centralizer hg.1).symm.trans h1) hne
    have := Q.theta_mul hgK (one_mem (Xt0 a y ⊓ C[z]))
    rw [mul_one, iso_map_one P.hZ, mul_one] at this
    exact this.symm
  have hvt0 : ∀ g ∈ C[a] ⊓ Xt0 a y, A g = asegTheta A Z a y z g := by
    intro g hg
    obtain ⟨k, hk, w, hw, rfl⟩ := Q.dec g hg.2
    have hwA : w ∈ C[a] := by
      have : k⁻¹ * (k * w) = w := by group
      rw [← this]
      exact (C[a]).mul_mem ((C[a]).inv_mem hk.1) hg.1
    rw [Q.theta_mul hk hw, P.hA.map_mul k hk.1 w hwA, ← P.Z_eq_A w ⟨hwA, hw.2⟩]
  have hvt1 : ∀ g ∈ C[a] ⊓ Xt1 a y z, A g = Z g := fun g hg =>
    (P.Z_eq_A g ⟨hg.1, hg.2.1⟩).symm
  have het1 : ∀ g ∈ edgeStab (vertA a) (vertY D) ⊓ Xt1 a y z, asegTheta A Z a y z g = Z g := by
    intro g hg
    have hgW : g ∈ Xt0 a y ⊓ C[z] := ⟨edgeStab_le_Xt0 D h hg.1, hg.2.1⟩
    have := Q.theta_mul (one_mem (C[a] ⊓ C[y])) hgW
    rwa [one_mul, iso_map_one P.hA, one_mul] at this
  have hvt'0 : ∀ g ∈ C[a], A g ∈ Xt0 a' y' → g ∈ Xt0 a y := by
    intro g hg hmem
    have := mem_Xt0_iff_of_isIsoOn P.hA haC h.y_mem_cent_a hg
    rw [P.A_a, P.A_y] at this
    exact this.1 hmem
  have hvt'1 : ∀ g ∈ C[a], A g ∈ Xt1 a' y' z' → g ∈ Xt1 a y z := by
    intro g hg hmem
    have := mem_Xt1_iff_of_isIsoOn P.hA haC h.y_mem_cent_a h.z_mem_cent_a hg
    rw [P.A_a, P.A_y, P.A_z] at this
    exact this.1 hmem
  have het'1 : ∀ g ∈ edgeStab (vertA a) (vertY D), asegTheta A Z a y z g ∈ Xt1 a' y' z' →
      g ∈ Xt1 a y z := by
    intro g hg hmem
    obtain ⟨k, hk, w, hw, rfl⟩ := Q.dec g (edgeStab_le_Xt0 D h hg)
    rw [Q.theta_mul hk hw] at hmem
    have hAk : A k ∈ C[A z] := by
      rw [P.A_z]
      have h1 : A k = (A k * Z w) * (Z w)⁻¹ := by group
      rw [h1]
      exact (C[z']).mul_mem hmem.1 ((C[z']).inv_mem (P.hZ.map_mem w hw.2))
    have hkz : k ∈ C[z] := (iso_mem_centralizer_iff P.hA hk.1 h.z_mem_cent_a).1 hAk
    exact edgeStab_inf_le_Xt1 D h ⟨hg, (C[z]).mul_mem hkz hw.2⟩
  exact ⟨P.hA, he, fun j => by cases j; exacts [hθ, hZ1], hve,
    fun j => by cases j; exacts [hvt0, hvt1], fun j => by cases j; exacts [fun g _ => rfl, het1],
    fun g hg hmem => (hEA g hg).1 hmem, fun j => by cases j; exacts [hvt'0, hvt'1],
    fun j => by cases j; exacts [fun g hg _ => edgeStab_le_Xt0 D h hg, het'1]⟩

end Assemble

end CFSG.Monster.GMS
