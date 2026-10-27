module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpDefs
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeTypeA
public import CFSG.ClassicalInvolution.WeakCT.Torus
import CFSG.LocalAnalysis.EvenBN.U4.Model.Perfect
public import CFSG.ClassicalInvolution.WeakCT.StandardPair

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.LieType.Universal.Symplectic (equivStatedSp)
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G]

section Coord

variable {p n : ℕ}

@[expose] def ggBsCoordEq (Bs : Subgroup G) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (i j : Fin n) : Subgroup G :=
  (MonoidHom.eqLocus ((Pi.evalMonoidHom (fun _ => Multiplicative (ZMod p)) i).comp
    eta.toMonoidHom) ((Pi.evalMonoidHom (fun _ => Multiplicative (ZMod p)) j).comp
    eta.toMonoidHom)).map Bs.subtype

@[expose] def ggBsCoordZero (Bs : Subgroup G) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (j : Fin n) : Subgroup G :=
  ((Pi.evalMonoidHom (fun _ => Multiplicative (ZMod p)) j).comp eta.toMonoidHom).ker.map
    Bs.subtype

variable {Bs : Subgroup G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}

theorem mem_ggBsCoordEq {i j : Fin n} {g : G} :
    g ∈ ggBsCoordEq Bs eta i j ↔ ∃ h : g ∈ Bs, eta ⟨g, h⟩ i = eta ⟨g, h⟩ j := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b.2, hb⟩
  · rintro ⟨h, hg⟩
    exact ⟨⟨g, h⟩, hg, rfl⟩

theorem ggBsCoordEq_comm (i j : Fin n) : ggBsCoordEq Bs eta i j = ggBsCoordEq Bs eta j i := by
  ext g
  rw [mem_ggBsCoordEq, mem_ggBsCoordEq]
  exact ⟨fun ⟨h, he⟩ => ⟨h, he.symm⟩, fun ⟨h, he⟩ => ⟨h, he.symm⟩⟩

theorem mem_ggBsCoordZero {j : Fin n} {g : G} :
    g ∈ ggBsCoordZero Bs eta j ↔ ∃ h : g ∈ Bs, eta ⟨g, h⟩ j = 1 := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b.2, hb⟩
  · rintro ⟨h, hg⟩
    exact ⟨⟨g, h⟩, hg, rfl⟩

theorem coe_mem_ggBsCoordEq {i j : Fin n} {b : ↥Bs} :
    (b : G) ∈ ggBsCoordEq Bs eta i j ↔ eta b i = eta b j :=
  mem_ggBsCoordEq.trans ⟨fun ⟨_, h⟩ => h, fun h => ⟨b.2, h⟩⟩

theorem coe_mem_ggBsCoordZero {j : Fin n} {b : ↥Bs} :
    (b : G) ∈ ggBsCoordZero Bs eta j ↔ eta b j = 1 :=
  mem_ggBsCoordZero.trans ⟨fun ⟨_, h⟩ => h, fun h => ⟨b.2, h⟩⟩

theorem ggBsCoordEq_le (i j : Fin n) : ggBsCoordEq Bs eta i j ≤ Bs :=
  Subgroup.map_subtype_le _

theorem ggBsCoordZero_le (j : Fin n) : ggBsCoordZero Bs eta j ≤ Bs :=
  Subgroup.map_subtype_le _

end Coord

section Commutator

private theorem conj_mem_commutator_self {D : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.normalizer (D : Set G)) {w : G} (hw : w ∈ ⁅D, D⁆) :
    c * w * c⁻¹ ∈ ⁅D, D⁆ := by
  have hle : ⁅D, D⁆ ≤ ⁅D, D⁆.comap (MulAut.conj c).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have ha' : c * a * c⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hc a).mp ha
    have hb' : c * b * c⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hc b).mp hb
    have e : (MulAut.conj c).toMonoidHom ⁅a, b⁆ = ⁅c * a * c⁻¹, c * b * c⁻¹⁆ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
      group
    rw [Subgroup.mem_comap, e]
    exact Subgroup.commutator_mem_commutator ha' hb'
  simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hle hw

theorem ggCommutator_centralizer_eq {E H X R : Subgroup G} {t : G}
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hHE : H ≤ E) (htE : t ∈ E)
    (hgen : ∀ e ∈ E, ∃ h ∈ H, ∃ k : ℤ, e = h * t ^ k)
    (hX : Subgroup.centralizer (H : Set G) ≤ Subgroup.normalizer (X : Set G))
    (ht : t ∈ ⁅X ⊓ Subgroup.centralizer (H : Set G), X ⊓ Subgroup.centralizer (H : Set G)⁆)
    (hDR : ⁅X ⊓ Subgroup.centralizer (H : Set G), X ⊓ Subgroup.centralizer (H : Set G)⁆ ≤ R)
    (hRC : R ≤ Subgroup.centralizer (H : Set G)) (hRt : R ≤ ⁅R, Subgroup.zpowers t⁆) :
    ⁅Subgroup.centralizer (H : Set G), E⁆ = R := by
  set C := Subgroup.centralizer (H : Set G) with hCdef
  set D := X ⊓ C with hDdef
  have hND : ∀ c ∈ C, c ∈ Subgroup.normalizer (D : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro d
    have h1 := Subgroup.mem_normalizer_iff.mp (hX hc) d
    have h2 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hc) d
    exact ⟨fun hd => ⟨h1.mp hd.1, h2.mp hd.2⟩, fun hd => ⟨h1.mpr hd.1, h2.mpr hd.2⟩⟩
  have hHC : H ≤ C := fun h hh => Subgroup.mem_centralizer_iff.mpr fun h' hh' =>
    hEc h' (hHE hh') h (hHE hh)
  refine le_antisymm ?_ (hRt.trans (Subgroup.commutator_mono hRC (Subgroup.zpowers_le.mpr htE)))
  rw [Subgroup.commutator_le]
  intro c hc e he
  obtain ⟨h, hh, k, rfl⟩ := hgen e he
  apply hDR
  have hch : c * h = h * c := (Subgroup.mem_centralizer_iff.mp hc h hh).symm
  have htk : t ^ k ∈ ⁅D, D⁆ := Subgroup.zpow_mem _ ht k
  have h1 : c * t ^ k * c⁻¹ ∈ ⁅D, D⁆ := conj_mem_commutator_self (hND c hc) htk
  have h2 : c * t ^ k * c⁻¹ * (t ^ k)⁻¹ ∈ ⁅D, D⁆ := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ htk)
  have e : ⁅c, h * t ^ k⁆ = h * (c * t ^ k * c⁻¹ * (t ^ k)⁻¹) * h⁻¹ := by
    rw [commutatorElement_def]
    calc c * (h * t ^ k) * c⁻¹ * (h * t ^ k)⁻¹ = (c * h) * t ^ k * c⁻¹ * (t ^ k)⁻¹ * h⁻¹ := by
          group
      _ = (h * c) * t ^ k * c⁻¹ * (t ^ k)⁻¹ * h⁻¹ := by rw [hch]
      _ = h * (c * t ^ k * c⁻¹ * (t ^ k)⁻¹) * h⁻¹ := by group
  rw [e]
  exact conj_mem_commutator_self (hND h (hHC hh)) h2

end Commutator

section RootSL2

open CFSG.ClassicalInvolution.WeakCT (torusHom)
open CFSG.LocalAnalysis.EvenBN.U4 (diagSL2 upperSL2 lowerSL2 commutator_diagSL2_upperSL2
  commutator_diagSL2_lowerSL2 mem_of_lowerSL2_upperSL2)

theorem ggRange_le_commutator_zpowers_torusHom {F : Type} [Field F] (ψ : SL(2, F) →* G)
    {ζ : Fˣ} (hζ : (ζ : F) ^ 2 ≠ 1) :
    ψ.range ≤ ⁅ψ.range, Subgroup.zpowers (ψ (torusHom F ζ))⁆ := by
  have hdiag : torusHom F ζ = diagSL2 ζ := by
    refine Subtype.ext ?_
    show !![(ζ : F), 0; 0, ((ζ⁻¹ : Fˣ) : F)] = !![(ζ : F), 0; 0, (ζ : F)⁻¹]
    rw [Units.val_inv_eq_inv_val]
  have hl1 : (ζ : F) ^ 2 - 1 ≠ 0 := sub_ne_zero.2 hζ
  have hl2 : ((ζ : F) ^ 2)⁻¹ - 1 ≠ 0 := sub_ne_zero.2 fun e => hζ (inv_eq_one.1 e)
  rw [Subgroup.commutator_comm, hdiag]
  rintro _ ⟨m, rfl⟩
  refine mem_of_lowerSL2_upperSL2 ψ (fun b => ?_) (fun s => ?_) m
  · have e : lowerSL2 b = ⁅diagSL2 ζ, lowerSL2 (b / (((ζ : F) ^ 2)⁻¹ - 1))⁆ := by
      rw [commutator_diagSL2_lowerSL2, mul_div_cancel₀ _ hl2]
    rw [e, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers _) ⟨_, rfl⟩
  · have e : upperSL2 s = ⁅diagSL2 ζ, upperSL2 (s / ((ζ : F) ^ 2 - 1))⁆ := by
      rw [commutator_diagSL2_upperSL2, mul_div_cancel₀ _ hl1]
    rw [e, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers _) ⟨_, rfl⟩

end RootSL2

section Frames

variable {p n r f : ℕ}

@[expose] def GGSecFiveBPermSpLFrame (Bs L : Subgroup G)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (π : Fin (r + 2) ≃ Fin n)
    (σ : SL(r + 2, GaloisField 2 f) →* G)
    (χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ) : Prop :=
  σ.ker ≤ Subgroup.center SL(r + 2, GaloisField 2 f) ∧ σ.range = L ∧ Function.Injective χ ∧
    ∀ (b : ↥Bs) (u : SL(r + 2, GaloisField 2 f)),
      (b : G) * σ u * (b : G)⁻¹ =
        σ (InnerDiagA.conjSL (InnerDiagA.diagGL fun m => χ (eta b (π m))) u)

@[expose] noncomputable def ggSecFiveBPermSpKTorus {Bs : Subgroup G}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (π : Fin (r + 2) ≃ Fin n)
    (χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ) (b : ↥Bs) :
    StatedSp (r + 1) (GaloisField 2 f) :=
  equivStatedSp (r + 1) (GaloisField 2 f)
    (TauCeti.GLSymplecticFin.diagonal fun m => χ (eta b (π m.succ)))

@[expose] def GGSecFiveBPermSpKFrame (Bs K : Subgroup G)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (π : Fin (r + 2) ≃ Fin n)
    (κ : StatedSp (r + 1) (GaloisField 2 f) →* G)
    (χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ) : Prop :=
  Function.Injective κ ∧ κ.range = K ∧ Function.Injective χ ∧
    ∀ (b : ↥Bs) (s : StatedSp (r + 1) (GaloisField 2 f)),
      (b : G) * κ s * (b : G)⁻¹ =
        κ (ggSecFiveBPermSpKTorus eta π χ b * s * (ggSecFiveBPermSpKTorus eta π χ b)⁻¹)

theorem GGSecFiveBPermSpKFrame.conj_transporter
    {G : Type} [Group G] {p n r f : ℕ} {Bs L : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {κ : StatedSp (r + 1) (GaloisField 2 f) →* G}
    {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hF : GGSecFiveBPermSpKFrame Bs L eta π κ χ)
    (φ : MulAut ↥Bs) (g : G) (τ : Equiv.Perm (Fin n))
    (hact : ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = g * b * g⁻¹)
    (hcoord : ∀ (b : ↥Bs) (i : Fin n), eta (φ b) (τ i) = eta b i) :
    GGSecFiveBPermSpKFrame Bs (L.map (MulAut.conj g).toMonoidHom) eta (π.trans τ)
      ((MulAut.conj g).toMonoidHom.comp κ) χ := by
  have hinv : ∀ b : ↥Bs, g⁻¹ * (b : G) * g = ((φ.symm b : ↥Bs) : G) := by
    intro b
    have h := hact (φ.symm b)
    rw [φ.apply_symm_apply] at h
    rw [h]
    group
  have hT : ∀ b : ↥Bs, ggSecFiveBPermSpKTorus eta π χ (φ.symm b) =
      ggSecFiveBPermSpKTorus eta (π.trans τ) χ b := by
    intro b
    have hc : (fun m : Fin (r + 1) => χ (eta (φ.symm b) (π m.succ))) =
        (fun m : Fin (r + 1) => χ (eta b ((π.trans τ) m.succ))) := by
      funext m
      have h := hcoord (φ.symm b) (π m.succ)
      rw [φ.apply_symm_apply] at h
      exact congrArg χ h.symm
    simp only [ggSecFiveBPermSpKTorus, hc]
  refine ⟨(MulAut.conj g).injective.comp hF.1, ?_, hF.2.2.1, ?_⟩
  · rw [MonoidHom.range_comp, hF.2.1]
  · intro b s
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc (b : G) * (g * κ s * g⁻¹) * (b : G)⁻¹ =
          g * ((g⁻¹ * (b : G) * g) * κ s * (g⁻¹ * (b : G) * g)⁻¹) * g⁻¹ := by group
      _ = g * κ (ggSecFiveBPermSpKTorus eta π χ (φ.symm b) * s *
          (ggSecFiveBPermSpKTorus eta π χ (φ.symm b))⁻¹) * g⁻¹ := by
            rw [hinv, hF.2.2.2]
      _ = _ := by rw [hT]

end Frames

section Inputs

@[expose] def GGSecFiveBPermSpLFrameInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (n : ℕ) (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e → 4 ≤ n →
      ∀ eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)),
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p →
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p →
        (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
          ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) →
        ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K →
      ∀ (f : ℕ) (K : Subgroup G) (i0 : Fin n), GGSecFiveBPermSpCell p Bs L 𝒦 n eta f K i0 →
        ∀ (r : ℕ) (π : Fin (r + 2) ≃ Fin n), ∃ (σ : SL(r + 2, GaloisField 2 f) →* G)
          (χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ), GGSecFiveBPermSpLFrame Bs L eta π σ χ

@[expose] def GGSecFiveBPermSpKFrameInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (n : ℕ) (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e → 4 ≤ n →
      ∀ eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)),
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p →
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p →
        (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
          ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) →
        ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K →
      ∀ (f : ℕ) (K : Subgroup G) (i0 : Fin n), GGSecFiveBPermSpCell p Bs L 𝒦 n eta f K i0 →
        ∃ (r : ℕ) (π : Fin (r + 2) ≃ Fin n), π 0 = i0 ∧
          ∃ (κ : StatedSp (r + 1) (GaloisField 2 f) →* G)
            (χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ),
            GGSecFiveBPermSpKFrame Bs K eta π κ χ

end Inputs

noncomputable abbrev ggSecFiveBZeta {p f : ℕ}
    (χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ) : (GaloisField 2 f)ˣ :=
  χ (Multiplicative.ofAdd 1)

section TorusParam

variable {p f : ℕ} [Fact p.Prime]

theorem ggSecFiveBTwo_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ 2 := by
    have h' : ((2 : ℕ) : ZMod p) = 0 := h
    exact (CharP.cast_eq_zero_iff (ZMod p) p 2).1 h'
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1
  · exact (Fact.out : p.Prime).ne_one h1
  · exact hp2 h1

theorem ggSecFiveBToAdd_mul (u v : Multiplicative (ZMod p)) :
    Multiplicative.toAdd (u * v) = Multiplicative.toAdd u + Multiplicative.toAdd v := rfl

theorem ggSecFiveBToAdd_sq (u : Multiplicative (ZMod p)) :
    Multiplicative.toAdd (u ^ 2) = 2 * Multiplicative.toAdd u := by
  rw [pow_two, ggSecFiveBToAdd_mul]
  ring

theorem ggSecFiveBOfAdd_add (a b : ZMod p) :
    Multiplicative.ofAdd (a + b) = Multiplicative.ofAdd a * Multiplicative.ofAdd b := rfl

theorem ggSecFiveBOfAdd_nsmul (a : ZMod p) (k : ℕ) :
    Multiplicative.ofAdd (k • a) = (Multiplicative.ofAdd a) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [succ_nsmul, ggSecFiveBOfAdd_add, ih, pow_succ]

theorem ggSecFiveBToAdd_pow (a : ZMod p) (k : ℕ) :
    Multiplicative.toAdd ((Multiplicative.ofAdd a) ^ k) = k • a := by
  rw [← ggSecFiveBOfAdd_nsmul]
  rfl

theorem ggSecFiveBZeta_pow_p {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ} :
    ggSecFiveBZeta χ ^ p = 1 := by
  have hp1 : (p : ℕ) • (1 : ZMod p) = 0 := by
    rw [nsmul_eq_mul, mul_one, ZMod.natCast_self]
  rw [ggSecFiveBZeta, ← map_pow, ← ggSecFiveBOfAdd_nsmul, hp1]
  exact map_one χ

theorem ggSecFiveBZeta_ne_one {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hχ : Function.Injective χ) : ggSecFiveBZeta χ ≠ 1 := by
  intro h
  have h' : χ (Multiplicative.ofAdd 1) = χ 1 := h.trans (map_one χ).symm
  have h2 : (1 : ZMod p) = 0 := by
    simpa using congrArg Multiplicative.toAdd (hχ h')
  exact one_ne_zero h2

theorem ggSecFiveBZeta_ne_inv {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hχ : Function.Injective χ) (hp2 : p ≠ 2) :
    ggSecFiveBZeta χ ≠ (ggSecFiveBZeta χ)⁻¹ := by
  intro h
  have h' : χ (Multiplicative.ofAdd 1) = χ (Multiplicative.ofAdd (-1)) := by
    rw [ggSecFiveBZeta] at h
    rw [h, ← map_inv]
    congr 1
  have h2 := hχ h'
  have h3 : ((1 : ZMod p)) = -1 := by
    have := congrArg Multiplicative.toAdd h2
    simpa using this
  have h4 : (2 : ZMod p) = 0 := by
    have h5 : (1 : ZMod p) + 1 = 0 := by
      nth_rewrite 1 [h3]
      exact neg_add_cancel 1
    calc (2 : ZMod p) = 1 + 1 := by ring
      _ = 0 := h5
  exact ggSecFiveBTwo_ne_zero_zmod (p := p) hp2 h4

theorem ggSecFiveBChi_sq_inj {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hp2 : p ≠ 2) (hχ : Function.Injective χ)
    {u v : Multiplicative (ZMod p)} (h : χ u ^ 2 = χ v ^ 2) : u = v := by
  have h2 : χ (u ^ 2) = χ (v ^ 2) := by rw [map_pow, map_pow, h]
  have h3 : u ^ 2 = v ^ 2 := hχ h2
  have h5 : (2 : ZMod p) * (Multiplicative.toAdd u) = 2 * Multiplicative.toAdd v := by
    have := congrArg Multiplicative.toAdd h3
    rwa [ggSecFiveBToAdd_sq, ggSecFiveBToAdd_sq] at this
  have h6 : Multiplicative.toAdd u = Multiplicative.toAdd v := by
    have h0 : (2 : ZMod p) * (Multiplicative.toAdd u - Multiplicative.toAdd v) = 0 := by
      rw [mul_sub, h5, sub_self]
    rcases mul_eq_zero.1 h0 with h' | h'
    · exact absurd h' (ggSecFiveBTwo_ne_zero_zmod (p := p) hp2)
    · exact sub_eq_zero.1 h'
  exact Multiplicative.toAdd.injective h6

theorem ggSecFiveBZeta_sq_ne_one {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hp2 : p ≠ 2) (hχ : Function.Injective χ) :
    ((ggSecFiveBZeta χ : (GaloisField 2 f)ˣ) : GaloisField 2 f) ^ 2 ≠ 1 := by
  intro h
  have h1 : ggSecFiveBZeta χ ^ 2 = (1 : (GaloisField 2 f)ˣ) := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, h, Units.val_one]
  have h2 : χ (Multiplicative.ofAdd 1) ^ 2 = χ (1 : Multiplicative (ZMod p)) ^ 2 := by
    rw [map_one χ, one_pow]
    exact h1
  have h3 : Multiplicative.ofAdd (1 : ZMod p) = (1 : Multiplicative (ZMod p)) :=
    ggSecFiveBChi_sq_inj (χ := χ) hp2 hχ h2
  have h4 := congrArg Multiplicative.toAdd h3
  simp at h4

end TorusParam

section BsLemmas

variable {G : Type} [Group G] {Bs : Subgroup G}

theorem ggSecFiveBSubtype_mul_inv_pow {e t : G} (he : e ∈ Bs) (ht : t ∈ Bs) (n : ℕ) :
    (⟨e * (t ^ n)⁻¹, Subgroup.mul_mem Bs he (Subgroup.inv_mem Bs (Subgroup.pow_mem Bs ht n))⟩ :
        ↥Bs) = ⟨e, he⟩ * (⟨t, ht⟩ ^ n)⁻¹ := by
  refine Subtype.ext ?_
  simp [Subgroup.coe_mul]

theorem ggSecFiveBEta_subtype_mul_inv_pow {p n : ℕ}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {e t : G} (he : e ∈ Bs) (ht : t ∈ Bs) (k : ℕ) :
    eta ⟨e * (t ^ k)⁻¹, Subgroup.mul_mem Bs he (Subgroup.inv_mem Bs (Subgroup.pow_mem Bs ht k))⟩ =
      eta ⟨e, he⟩ * ((eta ⟨t, ht⟩) ^ k)⁻¹ := by
  rw [ggSecFiveBSubtype_mul_inv_pow, map_mul, map_inv, map_pow]

theorem ggSecFiveBHgen_long {p n r : ℕ} [Fact p.Prime]
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {t : G} (htB : t ∈ Bs) {j : Fin (r + 1)}
    (hηt : ∀ m, eta ⟨t, htB⟩ (π m.succ) = if m = j then Multiplicative.ofAdd 1 else 1) :
    ∀ e ∈ Bs, ∃ h ∈ ggBsCoordZero Bs eta (π j.succ), ∃ k : ℤ, e = h * t ^ k := by
  intro e he
  let n₀ : ℕ := (Multiplicative.toAdd (eta ⟨e, he⟩ (π j.succ))).val
  refine ⟨e * (t ^ n₀)⁻¹, ?_, (n₀ : ℤ), ?_⟩
  · rw [mem_ggBsCoordZero]
    have hmem : e * (t ^ n₀)⁻¹ ∈ Bs :=
      Subgroup.mul_mem Bs he (Subgroup.inv_mem Bs (Subgroup.pow_mem Bs htB n₀))
    refine ⟨hmem, ?_⟩
    have h1 : eta ⟨e * (t ^ n₀)⁻¹, hmem⟩ = eta ⟨e, he⟩ * ((eta ⟨t, htB⟩) ^ n₀)⁻¹ :=
      ggSecFiveBEta_subtype_mul_inv_pow he htB n₀
    rw [h1, Pi.mul_apply, Pi.inv_apply, Pi.pow_apply, hηt j]
    simp only [if_true]
    refine Multiplicative.toAdd.injective ?_
    rw [ggSecFiveBToAdd_mul, toAdd_inv, ggSecFiveBToAdd_pow]
    rw [show n₀ • (1 : ZMod p) = (n₀ : ZMod p) from by rw [nsmul_eq_mul, mul_one],
      ZMod.natCast_zmod_val,
      show Multiplicative.toAdd (1 : Multiplicative (ZMod p)) = 0 from rfl]
    abel
  · rw [zpow_natCast, mul_assoc, inv_mul_cancel, mul_one]

theorem ggSecFiveBTorusHom_ne_one {f : ℕ} {ζ : (GaloisField 2 f)ˣ}
    (h : (ζ : GaloisField 2 f) ≠ 1) :
    CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) ζ ≠ 1 := by
  intro hh
  apply h
  have := congrFun (congrFun (congrArg (fun x : SL(2, GaloisField 2 f) =>
    ((x : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)))) hh) 0) 0
  simpa [CFSG.ClassicalInvolution.WeakCT.coe_torusHom] using this

theorem ggSecFiveBFour_le_card_galois {f : ℕ} (hf : 2 ≤ f) : 4 ≤ Nat.card (GaloisField 2 f) := by
  rw [GaloisField.card 2 f (by omega)]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

end BsLemmas

end CFSG.StandardType

end
