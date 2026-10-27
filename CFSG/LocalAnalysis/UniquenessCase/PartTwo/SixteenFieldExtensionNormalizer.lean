module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Cent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Out
import CFSG.ClassicalGroups.Symplectic.InvariantForm
import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8SimMult
public import CFSG.Quasithin.Background.RealizesFaithful

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.RankThree.GF2n.Stroth80
open Matrix
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

theorem pSubgroup_le_of_sp4_natural_of_centralizer_eq_bot
    (hW : ∀ w : W, w ^ 2 = 1)
    {A H : Subgroup (MulAut W)}
    (hHA : H ≤ A)
    (hHn : A ≤ Subgroup.normalizer (H : Set (MulAut W)))
    (hcomm : commSub (⊤ : Subgroup W) H = ⊤)
    {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4 ∨ Nat.card K = 8)
    {p : ℕ} (hp : p = Nat.card K - 1)
    (hreal : (FFModel.nat (StatedSp 2 K)).Realizes H ⊤ (fixV H))
    (hcent : A ⊓ Subgroup.centralizer (H : Set (MulAut W)) = ⊥) :
    ∀ E : Subgroup (MulAut W), E ≤ A → IsPGroup p E → E ≤ H := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 := by
    rcases hK with h4 | h8
    · exact charP_of_card_eq_prime_pow (p := 2) (f := 2) (by
        rw [← Nat.card_eq_fintype_card, h4]; norm_num)
    · exact s16g_charP_two h8
  haveI : CharP K 2 := hchar
  have hfour : ∃ s : Finset K, s.card = 4 := by
    have hcard : 4 ≤ (Finset.univ : Finset K).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      rcases hK with h4 | h8 <;> omega
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4) hcard
    exact ⟨s, hs⟩
  have hperfΓ : Group.IsPerfect ↥(StatedSp 2 K) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp 2 K (Or.inl hfour)
  haveI : Group.IsPerfect (FFModel.nat (StatedSp 2 K)).Gam := hperfΓ
  have hrealEmbed := hreal
  obtain ⟨π, hπ⟩ := hreal
  have hπsurj : Function.Surjective π := hπ.1
  have hπinj : Function.Injective π :=
    FFModel.RealizesVia.injective_of_faithful_on (FFModel.nat_faithful (StatedSp 2 K)) hπ
  have hHperf : Group.IsPerfect ↥H :=
    Group.IsPerfect.ofSurjective (f := π) hπsurj
  have hHn' : ∀ a ∈ A, ∀ h ∈ H, a * h * a⁻¹ ∈ H := by
    intro a ha h hh
    exact ((Subgroup.mem_normalizer_iff.mp (hHn ha)) h).1 hh
  obtain ⟨ρ, hρinj, hρnorm⟩ :=
    s16g_exists_embedding (ι := Fin 2 ⊕ Fin 2) (K := K) (Γ := StatedSp 2 K)
      hHA hHn' hrealEmbed hcomm
  have hΓ : AddCommutantScalar (StatedSp 2 K) :=
    CFSG.RankThree.GF2n.Stroth80.addCommutantScalar_statedSp (m := 2) (K := K)
  have hcycRA : IsCyclic (RingAut K) := by
    rcases hK with h4 | h8
    · exact (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K
        (n := 2) (by rw [h4]; norm_num)).2
    · exact (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K
        (n := 3) (by rw [h8]; norm_num)).2
  have hcommRA : ∀ a b : RingAut K, a * b = b * a :=
    fun a b => (IsCyclic.commGroup (α := RingAut K)).mul_comm a b
  have hHsubPerf : Group.IsPerfect ↥(H.subgroupOf A) := by
    haveI : Group.IsPerfect ↥H := hHperf
    let e : (H.subgroupOf A) ≃* ↥H := Subgroup.subgroupOfEquivOfLe hHA
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let Eimg : Subgroup (MulAut (Multiplicative (Fin 2 ⊕ Fin 2 → K))) := (H.subgroupOf A).map ρ
  have hEimgPerf : Group.IsPerfect ↥Eimg := by
    haveI : Group.IsPerfect ↥(H.subgroupOf A) := hHsubPerf
    change Group.IsPerfect ↥((H.subgroupOf A).map ρ)
    exact Group.IsPerfect.map (H := H.subgroupOf A) (f := ρ)
  have hEimgNorm : Eimg ≤ s16gNorm (StatedSp 2 K) := by
    rintro x ⟨a, -, rfl⟩
    exact hρnorm a
  have hEimgTriv : ∀ φ : ↥Eimg →* RingAut K, φ = 1 := by
    intro φ
    haveI : Group.IsPerfect ↥Eimg := hEimgPerf
    haveI : IsMulCommutative (RingAut K) := IsMulCommutative.mk ⟨fun a b => hcommRA a b⟩
    haveI : Group.IsPerfect ↥φ.range := Group.IsPerfect.range (f := φ)
    haveI : IsMulCommutative ↥φ.range := inferInstance
    have hsub : Subsingleton ↥φ.range :=
      Group.IsPerfect.subsingleton_of_isMulCommutative (G := ↥φ.range)
    exact MonoidHom.range_eq_bot_iff.mp (Subgroup.eq_bot_of_subsingleton (H := φ.range))
  have hEimgLin : Eimg ≤ s16gLin (Fin 2 ⊕ Fin 2) K :=
    s16g_le_lin_of_hom_trivial (Γ := StatedSp 2 K) hΓ hEimgNorm hEimgTriv
  let Γimg : Subgroup (MulAut (Multiplicative (Fin 2 ⊕ Fin 2 → K))) :=
    (StatedSp 2 K).map (s16gNatHom (Fin 2 ⊕ Fin 2) K)
  have hEimgΓ : Eimg ≤ Γimg := by
    obtain ⟨F, hFN, hFmap⟩ := s16g_exists_matrix_subgroup hEimgNorm hEimgLin
    obtain ⟨μ, -, hμker⟩ := s16g_exists_mult_statedSp (m := 2) (K := K) (by norm_num)
    have hcommF : ⁅F, F⁆ ≤ StatedSp 2 K := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      let xN : ↥(Subgroup.normalizer (StatedSp 2 K : Set (GL (Fin 2 ⊕ Fin 2) K))) :=
        ⟨x, hFN hx⟩
      let yN : ↥(Subgroup.normalizer (StatedSp 2 K : Set (GL (Fin 2 ⊕ Fin 2) K))) :=
        ⟨y, hFN hy⟩
      have hμ : μ ⁅xN, yN⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm (μ xN) (μ yN))
      have hmem : ((⁅xN, yN⁆ :
          ↥(Subgroup.normalizer (StatedSp 2 K : Set (GL (Fin 2 ⊕ Fin 2) K)))) :
          GL (Fin 2 ⊕ Fin 2) K) ∈ StatedSp 2 K :=
        (hμker ⁅xN, yN⁆).mp hμ
      simpa [xN, yN, commutatorElement_def] using hmem
    have hmap : (⁅F, F⁆).map (s16gNatHom (Fin 2 ⊕ Fin 2) K) = ⁅Eimg, Eimg⁆ := by
      rw [Subgroup.map_commutator, hFmap]
    have hperfect : ⁅Eimg, Eimg⁆ = Eimg := Subgroup.isPerfect_iff.mp hEimgPerf
    calc Eimg = ⁅Eimg, Eimg⁆ := hperfect.symm
      _ = (⁅F, F⁆).map (s16gNatHom (Fin 2 ⊕ Fin 2) K) := hmap.symm
      _ ≤ Γimg := by
          dsimp only [Γimg]
          exact Subgroup.map_mono hcommF
  have hcardEimg : Nat.card Eimg = Nat.card ↥H := by
    dsimp only [Eimg]
    rw [Subgroup.card_map_of_injective (K := H.subgroupOf A) (f := ρ) hρinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHA).toEquiv
  have hcardΓH : Nat.card ↥(StatedSp 2 K) = Nat.card ↥H :=
    Nat.card_congr (MulEquiv.ofBijective π ⟨hπinj, hπsurj⟩).toEquiv
  have hcardΓimg : Nat.card Γimg = Nat.card ↥(StatedSp 2 K) := by
    dsimp only [Γimg]
    rw [Subgroup.card_map_of_injective (K := StatedSp 2 K)
      (f := s16gNatHom (Fin 2 ⊕ Fin 2) K)
      (s16gNatHom_injective (ι := Fin 2 ⊕ Fin 2) (K := K))]
  have hEimgEq : Eimg = Γimg :=
    Subgroup.eq_of_le_of_card_ge hEimgΓ (by rw [hcardΓimg, hcardΓH, hcardEimg])
  have hpPrime : p.Prime := by
    rcases hK with h4 | h8
    · rw [hp, h4]; norm_num
    · rw [hp, h8]; norm_num
  have hpAut : ¬ p ∣ Nat.card (RingAut K) := by
    rcases hK with h4 | h8
    · have h2 : Nat.card (RingAut K) = 2 :=
        (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K
          (n := 2) (by rw [h4]; norm_num)).1
      rw [hp, h4, h2]; norm_num
    · have h3 : Nat.card (RingAut K) = 3 :=
        (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K
          (n := 3) (by rw [h8]; norm_num)).1
      rw [hp, h8, h3]; norm_num
  intro E hEA hEp e he
  let EA : Subgroup ↥A := E.subgroupOf A
  have hEpA : IsPGroup p EA :=
    hEp.of_equiv (Subgroup.subgroupOfEquivOfLe hEA).symm
  have hEAImgP : IsPGroup p (EA.map ρ) := hEpA.map ρ
  have hEANorm : EA.map ρ ≤ s16gNorm (StatedSp 2 K) := by
    rintro x ⟨a, -, rfl⟩
    exact hρnorm a
  have hEALin : EA.map ρ ≤ s16gLin (Fin 2 ⊕ Fin 2) K :=
    s16g_le_lin_of_coprime (Γ := StatedSp 2 K) hΓ hpPrime hpAut hEANorm hEAImgP
  let a : ↥A := ⟨e, hEA he⟩
  have haEA : a ∈ EA := by
    rw [Subgroup.mem_subgroupOf]
    exact he
  have hρaLin : ρ a ∈ s16gLin (Fin 2 ⊕ Fin 2) K :=
    hEALin (Subgroup.mem_map.mpr ⟨a, haEA, rfl⟩)
  obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.mp (by simpa [s16gLin] using hρaLin)
  have hγnorm : γ ∈ Subgroup.normalizer (StatedSp 2 K : Set (GL (Fin 2 ⊕ Fin 2) K)) := by
    refine (s16g_mem_norm_natHom_iff (StatedSp 2 K) γ).mp ?_
    rw [hγ]
    exact hρnorm a
  have hγnorm' : ∀ A ∈ StatedSp 2 K, γ * A * γ⁻¹ ∈ StatedSp 2 K :=
    fun A hA => (Subgroup.mem_normalizer_iff.mp hγnorm A).1 hA
  obtain ⟨μ, s, hμ, hs, hsmul⟩ :=
    CFSG.ClassicalGroups.Symplectic.exists_smul_statedSp_of_normalizes (m := 2) (K := K)
      (by norm_num : 1 ≤ 2) hγnorm'
  have hsΓ : s16gNatHom (Fin 2 ⊕ Fin 2) K s ∈ Γimg := by
    dsimp only [Γimg]
    exact Subgroup.mem_map.mpr ⟨s, hs, rfl⟩
  have hsImg : s16gNatHom (Fin 2 ⊕ Fin 2) K s ∈ Eimg := by
    rw [hEimgEq]
    exact hsΓ
  obtain ⟨a_s, ha_s, hρas⟩ := Subgroup.mem_map.mp hsImg
  have hsH : (a_s : MulAut W) ∈ H := Subgroup.mem_subgroupOf.mp ha_s
  let c : ↥A := a * a_s⁻¹
  have hρc : ρ c = s16gNatHom (Fin 2 ⊕ Fin 2) K (γ * s⁻¹) := by
    calc ρ c = ρ a * (ρ a_s)⁻¹ := by simp only [c, map_mul, map_inv]
      _ = s16gNatHom (Fin 2 ⊕ Fin 2) K γ *
            (s16gNatHom (Fin 2 ⊕ Fin 2) K s)⁻¹ := by rw [hγ, hρas]
      _ = s16gNatHom (Fin 2 ⊕ Fin 2) K (γ * s⁻¹) := by rw [map_mul, map_inv]
  have hγs : ∀ x : Fin 2 ⊕ Fin 2 → K,
      ((γ * s⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ x =
        μ • x := by
    intro x
    have hx := hsmul (((s⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ x)
    calc ((γ * s⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ x
        = (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
            (((s⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ x) := by
            rw [Units.val_mul, ← Matrix.mulVec_mulVec]
      _ = μ • ((s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
            (((s⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ x)) := hx
      _ = μ • x := by
            rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
              Matrix.one_mulVec]
  have hτScalar : ∀ x : Multiplicative (Fin 2 ⊕ Fin 2 → K),
      s16gNatHom (Fin 2 ⊕ Fin 2) K (γ * s⁻¹) x = s16gSMul μ x := by
    intro x
    rw [s16gNatHom_apply, s16gSMul]
    exact congrArg Multiplicative.ofAdd (hγs (Multiplicative.toAdd x))
  have hτComm : ∀ t : GL (Fin 2 ⊕ Fin 2) K,
      s16gNatHom (Fin 2 ⊕ Fin 2) K (γ * s⁻¹) * s16gNatHom (Fin 2 ⊕ Fin 2) K t =
        s16gNatHom (Fin 2 ⊕ Fin 2) K t * s16gNatHom (Fin 2 ⊕ Fin 2) K (γ * s⁻¹) := by
    intro t
    ext x
    simp only [MulAut.mul_apply]
    rw [hτScalar ((s16gNatHom (Fin 2 ⊕ Fin 2) K t) x), hτScalar x]
    simp only [s16gSMul, s16gNatHom_apply, toAdd_ofAdd]
    rw [Matrix.mulVec_smul]
  have hcCentH : ∀ h ∈ H, (c : MulAut W) * h = h * (c : MulAut W) := by
    intro h hh
    have hhA : (⟨h, hHA hh⟩ : ↥A) ∈ H.subgroupOf A := by
      rw [Subgroup.mem_subgroupOf]
      exact hh
    have hρhE : ρ ⟨h, hHA hh⟩ ∈ Eimg :=
      Subgroup.mem_map.mpr ⟨⟨h, hHA hh⟩, hhA, rfl⟩
    have hρhLin : ρ ⟨h, hHA hh⟩ ∈ s16gLin (Fin 2 ⊕ Fin 2) K :=
      hEimgLin hρhE
    obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp (by simpa [s16gLin] using hρhLin)
    have hcommρ : ρ c * ρ ⟨h, hHA hh⟩ = ρ ⟨h, hHA hh⟩ * ρ c := by
      calc ρ c * ρ ⟨h, hHA hh⟩
          = s16gNatHom (Fin 2 ⊕ Fin 2) K (γ * s⁻¹) *
              s16gNatHom (Fin 2 ⊕ Fin 2) K t := by rw [hρc, ← ht]
        _ = s16gNatHom (Fin 2 ⊕ Fin 2) K t *
              s16gNatHom (Fin 2 ⊕ Fin 2) K (γ * s⁻¹) := hτComm t
        _ = ρ ⟨h, hHA hh⟩ * ρ c := by rw [hρc, ← ht]
    have hcommA : c * ⟨h, hHA hh⟩ = ⟨h, hHA hh⟩ * c := by
      apply hρinj
      calc ρ (c * ⟨h, hHA hh⟩) = ρ c * ρ ⟨h, hHA hh⟩ := map_mul ρ _ _
        _ = ρ ⟨h, hHA hh⟩ * ρ c := hcommρ
        _ = ρ (⟨h, hHA hh⟩ * c) := (map_mul ρ _ _).symm
    exact congrArg Subtype.val hcommA
  have hcCent : (c : MulAut W) ∈ Subgroup.centralizer (H : Set (MulAut W)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (hcCentH h hh).symm
  have hcBot : (c : MulAut W) = 1 := by
    have hmem : (c : MulAut W) ∈ (⊥ : Subgroup (MulAut W)) := by
      rw [← hcent]
      exact ⟨c.2, hcCent⟩
    exact Subgroup.mem_bot.mp hmem
  have hcOne : c = 1 := Subtype.ext hcBot
  have haEq : a = a_s := mul_inv_eq_one.mp hcOne
  have haVal : (a : MulAut W) = (a_s : MulAut W) := congrArg Subtype.val haEq
  have haMem : (a : MulAut W) ∈ H := by
    rwa [haVal]
  simpa [a] using haMem

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
