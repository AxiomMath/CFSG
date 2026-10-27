module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutDefs
public import CFSG.LocalAnalysis.StandardType.GGSixBstarRestSpFrame

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.LieType.Universal.Symplectic

namespace OrdPInnerSp

variable {n : ℕ} {F : Type} [Field F]

theorem frameDiag_commute (A₀ : StatedSp n F) (t t' : Fin n → Fˣ) :
    RestSp.frameDiag A₀ t * RestSp.frameDiag A₀ t' =
      RestSp.frameDiag A₀ t' * RestSp.frameDiag A₀ t := by
  have h : equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal t) *
      equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal t') =
        equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal t') *
          equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal t) := by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm t t']
  simp only [RestSp.frameDiag]
  calc A₀ * equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal t) * A₀⁻¹ *
        (A₀ * equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal t') * A₀⁻¹) =
      A₀ * (equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal t) *
        equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal t')) * A₀⁻¹ := by group
    _ = A₀ * (equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal t') *
        equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal t)) * A₀⁻¹ := by rw [h]
    _ = _ := by group

theorem conj_frameDiag (A₀ A₁ : StatedSp n F) (t : Fin n → Fˣ) :
    (A₁ * A₀⁻¹)⁻¹ * RestSp.frameDiag A₁ t * (A₁ * A₀⁻¹) = RestSp.frameDiag A₀ t := by
  simp only [RestSp.frameDiag]
  group

variable {f : ℕ}

theorem exists_frameDiag_of_pow (hf : 1 ≤ f) {p : ℕ} (hpp : p.Prime) (hp2 : p ≠ 2)
    (hp : p ∣ 2 ^ f - 1) (u : StatedSp n (GaloisField 2 f)) (hu : u ^ p = 1) :
    ∃ (A : StatedSp n (GaloisField 2 f)) (t : Fin n → (GaloisField 2 f)ˣ),
      u = RestSp.frameDiag A t := by
  have : Fact p.Prime := ⟨hpp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E : Subgroup (GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :=
    Subgroup.zpowers (u : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) with hE
  have hESp : E ≤ LargeEvenSpGroup (GaloisField 2 f) n := by
    rw [hE, Subgroup.zpowers_le]
    exact u.2
  have hu' : (u : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) ^ p = 1 := by
    rw [← Subgroup.coe_pow, hu, Subgroup.coe_one]
  have hEel : IsElemAbelian p E := by
    refine ⟨Subgroup.zpowers_isMulCommutative _, fun x hx => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hu',
      _root_.one_zpow]
  obtain ⟨ζ, hζ⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := GaloisField 2 f) (p := p)
    (by rw [GaloisField.card 2 f (by omega)]; exact hp)
  obtain ⟨P, hPSp, w, hw⟩ := TableBSymp.exists_symplectic_weight_basis_GL
    (TableBSymp.natCast_ne_zero_of_charTwo hpp hp2) hζ hESp hEel
  have hPSp' : P ∈ StatedSp n (GaloisField 2 f) := hPSp
  have huE : (u : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) ∈ E := Subgroup.mem_zpowers _
  refine ⟨⟨P, hPSp'⟩, fun i => w i ⟨_, huE⟩, ?_⟩
  apply Subtype.ext
  have h1 := hw ⟨_, huE⟩
  simp only [RestSp.frameDiag, Subgroup.coe_mul, Subgroup.coe_inv, RestSp.coe_equiv_diagonal]
  calc ((u : StatedSp n (GaloisField 2 f)) : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      (u : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) * P * P⁻¹ := by group
    _ = P * TauCeti.diagGL (TableBSymp.pairedUnits fun i => w i ⟨_, huE⟩) * P⁻¹ := by
        rw [show ((u : StatedSp n (GaloisField 2 f)) : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) *
          P = P * TauCeti.diagGL (TableBSymp.pairedUnits fun i => w i ⟨_, huE⟩) from h1]

theorem exists_conj_mem_centralizer_split {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs G₀ : Subgroup G} {ψ : StatedSp n (GaloisField 2 f) →* G}
    (hS : GGSixFusionSetting p Bs G₀ (Symplectic.rootDatum n (GaloisField 2 f)) .PSp n f ψ)
    (hp : p ∣ 2 ^ f - 1) {y : G} (hyp : y ^ p = 1)
    (hy : GGPsiInnerDiag (Symplectic.rootDatum n (GaloisField 2 f)) ψ y) :
    ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hadm, hrank⟩, ⟨hrange, hker⟩, -, -⟩ := hS.presents
  have hf : 1 ≤ f := hadm.2.1
  have hrk : 2 ≤ n := hrank
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hS.centralizer_eq_bot
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hz := hker ha
    rw [Symplectic.center_eq,
      CFSG.LieType.SteinbergBR.EvenSp.statedScalars_subgroupOf_statedSp (by omega)] at hz
    exact Subgroup.mem_bot.mp hz
  obtain ⟨A₀, hA₀⟩ := spFrame_core hf hrk ψ hker hC hS.prime hS.ne_two hS.elem hS.innerDiag hp
  obtain ⟨g, hg, hcg⟩ := PsiDiag.Symp.exists_mem_centralizer (F := GaloisField 2 f) hrk ψ hker hy
  rw [hC, Subgroup.mem_bot] at hcg
  have hyψ : y ∈ ψ.range := by
    rw [eq_inv_of_mul_eq_one_left hcg]
    exact ψ.range.inv_mem hg
  obtain ⟨u, rfl⟩ := hyψ
  have hup : u ^ p = 1 := hinj (by rw [map_pow, hyp, map_one])
  obtain ⟨A₁, t₁, rfl⟩ := exists_frameDiag_of_pow hf hS.prime hS.ne_two hp u hup
  refine ⟨ψ (A₁ * A₀⁻¹), Subgroup.le_normalizer (hrange ▸ ⟨_, rfl⟩), ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul, conj_frameDiag, Subgroup.mem_centralizer_iff]
  intro b hb
  obtain ⟨t, rfl⟩ := hA₀ b hb
  rw [← map_mul, ← map_mul, frameDiag_commute]

end OrdPInnerSp

section Family

theorem ggOrdPInnerConj_PSp_split : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs G₀ : Subgroup G)
    (n f : ℕ) (ψ : (ggU .PSp n f).K →* G),
    GGSixFusionSetting p Bs G₀ (ggU .PSp n f).D .PSp n f ψ → p ∣ 2 ^ f - 1 →
    ∀ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = p → GGPsiInnerDiag (ggU .PSp n f).D ψ y →
      ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G) := by
  intro G _ _ p Bs G₀ n f ψ hS hp y _ hyo hy
  have hyp : y ^ p = 1 := hyo ▸ pow_orderOf_eq_one y
  exact OrdPInnerSp.exists_conj_mem_centralizer_split hS hp hyp hy

@[expose] def GGOrdPInnerConjPSpNonsplit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs G₀ : Subgroup G) (n f : ℕ)
    (ψ : (ggU .PSp n f).K →* G),
    GGSixFusionSetting p Bs G₀ (ggU .PSp n f).D .PSp n f ψ →
    GGTwoLocalRankFour p (Subgroup.normalizer (G₀ : Set G)) → ¬ p ∣ 2 ^ f - 1 →
    ∀ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = p → GGPsiInnerDiag (ggU .PSp n f).D ψ y →
      ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G)

theorem ggOrdPInnerConjAt_PSp_of_nonsplit (h : GGOrdPInnerConjPSpNonsplit) :
    GGOrdPInnerConjAt .PSp := by
  intro G _ _ p Bs G₀ n f ψ hS h24 _ y hyM hyo hy
  by_cases hpq : p ∣ 2 ^ f - 1
  · exact ggOrdPInnerConj_PSp_split G p Bs G₀ n f ψ hS hpq y hyM hyo hy
  · exact h G p Bs G₀ n f ψ hS h24 hpq y hyM hyo hy

end Family

end CFSG.StandardType
