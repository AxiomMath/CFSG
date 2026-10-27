module

public import CFSG.LocalAnalysis.StandardType.GGK0ExcCentreEhat
public import CFSG.LocalAnalysis.StandardType.GGK0ExcCentreTorsionGamma
public import CFSG.LocalAnalysis.StandardType.GGK0ExcCentreCentral

public section

namespace CFSG.StandardType.GGK0ExcCentreU

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private lemma lk0xpb3_card_comap
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi)
    (Ehat : Subgroup (ModGL ρ.tau Omega)) (hEhat_le : Ehat ≤ ρ.iota.range) :
    Nat.card (Ehat.comap ρ.iota) = Nat.card Ehat := by
  calc Nat.card (Ehat.comap ρ.iota)
      = Nat.card ((Ehat.comap ρ.iota).map ρ.iota) :=
        (Subgroup.card_map_of_injective (K := Ehat.comap ρ.iota) (f := ρ.iota) ρ.iota_inj).symm
    _ = Nat.card Ehat := by rw [Subgroup.map_comap_eq_self hEhat_le]

private lemma lk0xpb3_isElemAbelian
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi)
    (Ehat : Subgroup (ModGL ρ.tau Omega))
    (hEhat : ∀ z ∈ Ehat, z ∈ ρ.setup.D.torus ∧ z ^ p = 1 ∧
      ∃ b : Fin ρ.tau.rank → Omegaˣ, rootDiagUnit ρ.tau b = z ∧
        ∀ γ ∈ kernelRoots (rootCharHom ρ.a), rootChar b γ = 1) :
    IsElemAbelian p (Ehat.comap ρ.iota) := by
  refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
  · intro x y
    have hx : ρ.iota (x : R) ∈ Ehat := Subgroup.mem_comap.mp x.2
    have hy : ρ.iota (y : R) ∈ Ehat := Subgroup.mem_comap.mp y.2
    obtain ⟨bx, hbx, -⟩ := (hEhat _ hx).2.2
    obtain ⟨by', hby', -⟩ := (hEhat _ hy).2.2
    apply Subtype.ext
    show (x : R) * (y : R) = (y : R) * (x : R)
    apply ρ.iota_inj
    rw [map_mul, map_mul, ← hbx, ← hby', ← rootDiagUnit_mul, ← rootDiagUnit_mul,
      mul_comm by' bx]
  · intro x hx
    apply ρ.iota_inj
    rw [map_pow, map_one]
    exact (hEhat _ (Subgroup.mem_comap.mp hx)).2.1

private lemma lk0xpb3_phi_fixed
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi)
    (Ehat : Subgroup (ModGL ρ.tau Omega))
    (hEhat : ∀ z ∈ Ehat, z ∈ ρ.setup.D.torus ∧ z ^ p = 1 ∧
      ∃ b : Fin ρ.tau.rank → Omegaˣ, rootDiagUnit ρ.tau b = z ∧
        ∀ γ ∈ kernelRoots (rootCharHom ρ.a), rootChar b γ = 1) :
    ∀ y ∈ Ehat.comap ρ.iota, phi y = y := by
  intro y hy
  have hyE : ρ.iota y ∈ Ehat := Subgroup.mem_comap.mp hy
  obtain ⟨b, hb, -⟩ := (hEhat _ hyE).2.2
  apply ρ.iota_inj
  have h1 : ρ.iota (phi y) =
      rootDiagUnit ρ.tau ρ.a * ρ.iota y * (rootDiagUnit ρ.tau ρ.a)⁻¹ :=
    (congrArg (fun f : MulAut R => ρ.iota (f y)) ρ.action_eq.symm).trans
      (ρ.modelAction_compat ⟨rootDiagUnit ρ.tau ρ.a, ρ.a_model⟩ y)
  rw [h1, ← hb]
  have hcomm : rootDiagUnit ρ.tau ρ.a * rootDiagUnit ρ.tau b =
      rootDiagUnit ρ.tau b * rootDiagUnit ρ.tau ρ.a := by
    rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm b ρ.a]
  rw [hcomm]
  group

private lemma lk0xpb3_central
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (hc : GGKacCentred lab p)
    (ρ : MarkedRationalKacRealization Omega lab p R I phi)
    (Ehat : Subgroup (ModGL ρ.tau Omega))
    (hEhat : ∀ z ∈ Ehat, z ∈ ρ.setup.D.torus ∧ z ^ p = 1 ∧
      ∃ b : Fin ρ.tau.rank → Omegaˣ, rootDiagUnit ρ.tau b = z ∧
        ∀ γ ∈ kernelRoots (rootCharHom ρ.a), rootChar b γ = 1) :
    ∀ y ∈ Ehat.comap ρ.iota, ∀ r : R, phi r = r → r * y = y * r := by
  intro y hy r hr
  have hyE : ρ.iota y ∈ Ehat := Subgroup.mem_comap.mp hy
  obtain ⟨b, hb, hχ⟩ := (hEhat _ hyE).2.2
  have hm_range : ρ.iota r ∈ ρ.iota.range := ⟨r, rfl⟩
  have hmΓ : ρ.iota r ∈ ρ.setup.Γ := by simpa [ρ.iota_range] using hm_range
  have hm_model : ρ.iota r ∈ ρ.setup.D.model :=
    (Subgroup.commutator_le_self (ρ.setup.D.model)) hmΓ
  have hm : ρ.iota r ∈ adjointGroup ρ.tau Omega := (ρ.setup.D.mem_model.mp hm_model).1
  have hphi : ρ.iota (phi r) =
      rootDiagUnit ρ.tau ρ.a * ρ.iota r * (rootDiagUnit ρ.tau ρ.a)⁻¹ :=
    (congrArg (fun f : MulAut R => ρ.iota (f r)) ρ.action_eq.symm).trans
      (ρ.modelAction_compat ⟨rootDiagUnit ρ.tau ρ.a, ρ.a_model⟩ r)
  have hmul : rootDiagUnit ρ.tau ρ.a * ρ.iota r * (rootDiagUnit ρ.tau ρ.a)⁻¹ = ρ.iota r := by
    rw [← hphi, hr]
  have hcomm : ρ.iota r * rootDiagUnit ρ.tau ρ.a = rootDiagUnit ρ.tau ρ.a * ρ.iota r := by
    have h2 : rootDiagUnit ρ.tau ρ.a * ρ.iota r =
        ρ.iota r * rootDiagUnit ρ.tau ρ.a := by
      calc rootDiagUnit ρ.tau ρ.a * ρ.iota r
          = rootDiagUnit ρ.tau ρ.a * ρ.iota r * (rootDiagUnit ρ.tau ρ.a)⁻¹ *
              rootDiagUnit ρ.tau ρ.a := by group
        _ = ρ.iota r * rootDiagUnit ρ.tau ρ.a := by rw [hmul]
    exact h2.symm
  apply ρ.iota_inj
  rw [map_mul, map_mul]
  exact PB2_central_in_centralizer (hc := hc) (ρ := ρ) (z := ρ.iota y)
    (hz := ⟨b, hb, hχ⟩) (m := ρ.iota r) (hm := hm) (hcomm := hcomm)

private lemma lk0xpb3_I_fixed
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (hc : GGKacCentred lab p)
    (ρ : MarkedRationalKacRealization Omega lab p R I phi)
    (Ehat : Subgroup (ModGL ρ.tau Omega))
    (hEhat : ∀ z ∈ Ehat, z ∈ ρ.setup.D.torus ∧ z ^ p = 1 ∧
      ∃ b : Fin ρ.tau.rank → Omegaˣ, rootDiagUnit ρ.tau b = z ∧
        ∀ γ ∈ kernelRoots (rootCharHom ρ.a), rootChar b γ = 1) :
    ∀ y ∈ Ehat.comap ρ.iota, ∀ g ∈ I, g * phi = phi * g → g y = y := by
  intro y hy g hgI hgphi
  have hyE : ρ.iota y ∈ Ehat := Subgroup.mem_comap.mp hy
  obtain ⟨b, hb, hχ⟩ := (hEhat _ hyE).2.2
  rw [← ρ.modelAction_range] at hgI
  obtain ⟨x, hx⟩ := hgI
  rw [← hx] at hgphi ⊢
  have hxmem : (x : ModGL ρ.tau Omega) ∈ adjointGroup ρ.tau Omega :=
    (ρ.setup.D.mem_model.mp x.2).1
  have hcomm : (x : ModGL ρ.tau Omega) * rootDiagUnit ρ.tau ρ.a =
      rootDiagUnit ρ.tau ρ.a * (x : ModGL ρ.tau Omega) := by
    have hgphi' : ρ.modelAction x * ρ.modelAction ⟨rootDiagUnit ρ.tau ρ.a, ρ.a_model⟩ =
        ρ.modelAction ⟨rootDiagUnit ρ.tau ρ.a, ρ.a_model⟩ * ρ.modelAction x :=
      (congrArg (fun f : MulAut R =>
        ρ.modelAction x * f = f * ρ.modelAction x) ρ.action_eq.symm).mp hgphi
    have h2 : ρ.modelAction (x * ⟨rootDiagUnit ρ.tau ρ.a, ρ.a_model⟩) =
        ρ.modelAction (⟨rootDiagUnit ρ.tau ρ.a, ρ.a_model⟩ * x) := by
      rw [map_mul, map_mul]
      exact hgphi'
    have h3 : x * ⟨rootDiagUnit ρ.tau ρ.a, ρ.a_model⟩ =
        ⟨rootDiagUnit ρ.tau ρ.a, ρ.a_model⟩ * x := ρ.modelAction_inj h2
    exact congrArg (fun w : ↥ρ.setup.D.model => (w : ModGL ρ.tau Omega)) h3
  have hP2 := PB2_central_in_centralizer (hc := hc) (ρ := ρ) (z := ρ.iota y)
    (hz := ⟨b, hb, hχ⟩) (m := (x : ModGL ρ.tau Omega)) (hm := hxmem) (hcomm := hcomm)
  apply ρ.iota_inj
  rw [ρ.modelAction_compat x y, hP2]
  group

theorem PB3_assembly
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (hpair : GGKacExcPair lab p) (hc : GGKacCentred lab p)
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) (hrz : 2 ≤ ρ.row.D.rZ)
    (hinner : ∀ g ∈ I, g ^ p = 1 → g ∈ (MulAut.conj : R →* MulAut R).range) :
    ∃ ER : Subgroup R, IsElemAbelian p ER ∧ Nat.card ER = p ^ ρ.row.D.rZ ∧
      (∀ y ∈ ER, phi y = y) ∧
      (∀ y ∈ ER, ∀ r : R, phi r = r → r * y = y * r) ∧
      (∀ y ∈ ER, ∀ g ∈ I, g * phi = phi * g → g y = y) := by
  obtain ⟨Ehat, hEhat, hcard⟩ := PA5_assembly hpair hc ρ hrz
  have hEhat_le : Ehat ≤ ρ.iota.range := fun z hz =>
    PB1_torsion_mem_iota_range ρ hinner z (hEhat z hz).1 (hEhat z hz).2.1
  refine ⟨Ehat.comap ρ.iota, lk0xpb3_isElemAbelian ρ Ehat hEhat, ?_,
    lk0xpb3_phi_fixed ρ Ehat hEhat, lk0xpb3_central hc ρ Ehat hEhat,
    lk0xpb3_I_fixed hc ρ Ehat hEhat⟩
  calc Nat.card (Ehat.comap ρ.iota) = Nat.card Ehat := lk0xpb3_card_comap ρ Ehat hEhat_le
    _ = p ^ ρ.row.D.rZ := hcard

end CFSG.StandardType.GGK0ExcCentreU

end
