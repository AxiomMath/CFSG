module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12MovesPlan

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] noncomputable def thetaC {G : Type} [Group G] [Finite G] (c : G) : Subgroup G :=
  inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G))

@[expose] def IsMaxThreeSub {G : Type} [Group G] (B Q : Subgroup G) : Prop :=
  IsPGroup 3 Q ∧ Q ≤ B ∧ ∀ R : Subgroup G, IsPGroup 3 R → R ≤ B → Q ≤ R → R = Q

@[expose] def S1red : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B F : Subgroup G), IsPGroup 3 F → F ≤ B →
    (∀ Q : Subgroup G, IsMaxThreeSub B Q → F ≤ Q →
      Nat.card {x : G // x ∈ Q ∧ x ^ 3 = 1} ≤ 81) →
    ∀ X : Subgroup G, IsPGroup 3 X → X ≤ B → Nat.card {x : G // x ∈ X ∧ x ^ 3 = 1} ≤ 81

@[expose] def S1N : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E F : Subgroup G) (a b : G)
    (R Y : Subgroup G), YCfg G A c L E F a b R Y → ∀ Q : Subgroup G, IsPGroup 3 Q →
      Q ≤ Subgroup.centralizer ({b} : Set G) → Q ≤ Subgroup.normalizer (Y : Set G)

@[expose] def S1gen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y : Subgroup G),
    inSubgroup (aschbacherSolvableCore 3) Y ≤ Y ∧
    inSubgroup (aschbacherSolvableCore 3) Y ≤ Sec4.thetaQuotCentralizer Y ∧
    ¬ 3 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) Y : Subgroup G) ∧
    Sec4.thetaQuotCentralizer Y ≤ Subgroup.normalizer (Y : Set G) ∧
    Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer (Sec4.thetaQuotCentralizer Y : Set G) ∧
    ∀ k ∈ Sec4.thetaQuotCentralizer Y, ∀ y ∈ Y,
      k * y * k⁻¹ * y⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) Y

@[expose] def S1Y : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E F : Subgroup G) (a b : G)
    (R Y : Subgroup G), YCfg G A c L E F a b R Y → M12Hyp Y →
      (Y ⊓ Sec4.thetaQuotCentralizer Y ≤ inSubgroup (aschbacherSolvableCore 3) Y) ∧
      (∀ P : Subgroup G, P ≤ Y → IsPGroup 3 P → Nat.card P ≤ 27 ∧ ∀ x ∈ P, x ^ 3 = 1) ∧
      (∃ P : Subgroup G, P ≤ Y ∧ IsPGroup 3 P ∧ Nat.card P = 27) ∧
      (∀ Q : Subgroup G, Q ≤ Subgroup.normalizer (Y : Set G) → IsPGroup 3 Q →
        Q ≤ Y ⊔ Sec4.thetaQuotCentralizer Y)

@[expose] def S1F : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E F : Subgroup G) (a b : G)
    (R Y : Subgroup G), YCfg G A c L E F a b R Y → M12Hyp Y →
      F = Subgroup.zpowers b ⊔ (F ⊓ Y) ∧
        F ⊓ Sec4.thetaQuotCentralizer Y ≤ Subgroup.zpowers b

@[expose] def S1abs : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Y K Θ F Q : Subgroup G) (b : G),
    IsMaxThreeSub B Q → F ≤ Q → Q ≤ Subgroup.centralizer ({b} : Set G) →
    Q ≤ Subgroup.normalizer (Y : Set G) → Y ≤ B →
    K ≤ Subgroup.normalizer (Y : Set G) →
    Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer (K : Set G) →
    Q ≤ Y ⊔ K →
    (∀ k ∈ K, ∀ y ∈ Y, k * y * k⁻¹ * y⁻¹ ∈ Θ) →
    Θ ≤ Y → Θ ≤ K → Y ⊓ K ≤ Θ → ¬ 3 ∣ Nat.card Θ →
    (∀ P : Subgroup G, P ≤ Y → IsPGroup 3 P → Nat.card P ≤ 27 ∧ ∀ x ∈ P, x ^ 3 = 1) →
    (∃ P : Subgroup G, P ≤ Y ∧ IsPGroup 3 P ∧ Nat.card P = 27) →
    CFSG.Assembly.IsElemAbelian 3 F →
    (∀ F' : Subgroup G, CFSG.Assembly.IsElemAbelian 3 F' → F ≤ F' → F' = F) →
    b ∈ F → F = Subgroup.zpowers b ⊔ (F ⊓ Y) → F ⊓ K ≤ Subgroup.zpowers b →
    Nat.card {x : G // x ∈ Q ∧ x ^ 3 = 1} ≤ 81

theorem S1_of_parts (h1 : S1red) (hN : S1N) (hgen : S1gen) (hY : S1Y) (hF : S1F)
    (hA : S1abs) : S1 := by
  intro G _ _ A c L E F a b R Y hY0 hM X hX hXC
  have hFe : CFSG.Assembly.IsElemAbelian 3 F := hY0.hD.isElemAbelian
  have hF3 : IsPGroup 3 F := fun g => ⟨1, Subtype.ext (by simpa using hFe.2 g g.2)⟩
  have hbF : b ∈ F := hY0.hD.mem_A
  have hFcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hFe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hFC : F ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hFcomm x hx b hbF)
  refine h1 G (Subgroup.centralizer ({b} : Set G)) F hF3 hFC (fun Q hQ hFQ => ?_) X hX hXC
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hgen G Y
  obtain ⟨y1, y2, y3, y4⟩ := hY G A c L E F a b R Y hY0 hM
  obtain ⟨f1, f2⟩ := hF G A c L E F a b R Y hY0 hM
  have hQC : Q ≤ Subgroup.centralizer ({b} : Set G) := hQ.2.1
  have hQN := hN G A c L E F a b R Y hY0 Q hQ.1 hQC
  have hYB : Y ≤ Subgroup.centralizer ({b} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hY0.hD.mem_thetaComponentsAt
  exact hA G (Subgroup.centralizer ({b} : Set G)) Y (Sec4.thetaQuotCentralizer Y)
    (inSubgroup (aschbacherSolvableCore 3) Y) F Q b hQ hFQ hQC hQN hYB g4 g5 (y4 Q hQN hQ.1) g6
    g1 g2 y1 g3 y2 y3 hFe (fun F' hF' hFF' => hY0.hD.eq_of_le hF' hFF') hbF f1 f2

@[expose] def S2d : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Θ E : Subgroup G) (b c v v' : G),
    ¬ 3 ∣ Nat.card Θ → CFSG.Assembly.IsElemAbelian 3 E → c ∈ E → b ∈ E →
    E ≤ Subgroup.normalizer (Θ : Set G) → v ∈ Subgroup.normalizer (Θ : Set G) →
    v' ∈ Subgroup.normalizer (Θ : Set G) →
    v ^ 3 ∈ Θ → v' ^ 3 ∈ Θ → v * v' * v⁻¹ * v'⁻¹ ∈ Θ →
    (∀ e ∈ E, v * e * v⁻¹ * e⁻¹ ∈ Subgroup.zpowers c ⊔ Θ) →
    (∀ e ∈ E, v' * e * v'⁻¹ * e⁻¹ ∈ Subgroup.zpowers c ⊔ Θ) →
    (v * v') * b * (v * v')⁻¹ * b⁻¹ ∈ Θ → v * v' ∉ E ⊔ Θ →
    ∃ ρ : G, (v * v')⁻¹ * ρ ∈ Θ ∧ ρ ^ 3 = 1 ∧ ρ ∈ Subgroup.normalizer (E : Set G) ∧
      ρ * b = b * ρ ∧ ρ ∉ E ∧ ∀ e ∈ E, ρ * e * ρ⁻¹ * e⁻¹ ∈ Subgroup.zpowers c

@[expose] def S2e : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E F : Subgroup G) (a b : G)
    (R Y : Subgroup G), YCfg G A c L E F a b R Y → ∀ v v' ρ : G, v ∈ L →
      v' ∈ Subgroup.centralizer ({c} : Set G) → (∀ l ∈ L, v' * l * v'⁻¹ * l⁻¹ ∈ thetaC c) →
      ρ ^ 3 = 1 → (v * v')⁻¹ * ρ ∈ thetaC c →
      ρ ∈ Subgroup.normalizer (L : Set G) ∧ ρ ∈ L ⊔ Sec4.thetaQuotCentralizer L

@[expose] def S2pair : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E F : Subgroup G) (a b : G)
    (R Y : Subgroup G), YCfg G A c L E F a b R Y →
      b ∉ E ⊓ Sec4.thetaQuotCentralizer L → b ∉ E ⊓ L →
      ∀ (t : G) (EY : Subgroup G), InvData E b c Y t EY →
        t ∉ Subgroup.normalizer (L : Set G) →
        ∃ v v' : G, v ∈ L ∧ v' ∈ Subgroup.centralizer ({c} : Set G) ∧ v ^ 3 = 1 ∧ v' ^ 3 = 1 ∧
          v * v' * v⁻¹ * v'⁻¹ ∈ thetaC c ∧ (∀ l ∈ L, v' * l * v'⁻¹ * l⁻¹ ∈ thetaC c) ∧
          (∀ e ∈ E, v * e * v⁻¹ * e⁻¹ ∈ Subgroup.zpowers c ⊔ thetaC c) ∧
          (∀ e ∈ E, v' * e * v'⁻¹ * e⁻¹ ∈ Subgroup.zpowers c ⊔ thetaC c) ∧
          (v * v') * b * (v * v')⁻¹ * b⁻¹ ∈ thetaC c ∧ v * v' ∉ E ⊔ thetaC c

theorem centralizer_le_normalizer_thetaC {G : Type} [Group G] [Finite G] (c : G) :
    Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (thetaC c : Set G) :=
  Sec6.le_normalizer_theta _

theorem thetaC_not_dvd {G : Type} [Group G] [Finite G] (c : G) : ¬ 3 ∣ Nat.card (thetaC c) :=
  (Sec6.theta_solvable_and_not_dvd (Subgroup.centralizer ({c} : Set G))).2

theorem S2_of_parts (h1 : S2pair) (h2 : S2d) (h3 : S2e) : S2 := by
  intro G _ _ A c L E F a b R Y hY hbC hbL t EY hd htL
  obtain ⟨v, v', hvL, hv'C, hv3, hv'3, hcomm, hL', hEv, hEv', hb, hnot⟩ :=
    h1 G A c L E F a b R Y hY hbC hbL t EY hd htL
  have hEe := hY.hCfg.hEe
  have hcE := hY.hcE
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hY.hCfg.hD.mem_thetaComponentsAt
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hEC : E ≤ Subgroup.centralizer ({c} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hEcomm x hx c hcE)
  have hNΘ := centralizer_le_normalizer_thetaC (G := G) c
  have h1Θ : ∀ x : G, x ^ 3 = 1 → x ^ 3 ∈ thetaC c := fun x hx => by
    rw [hx]
    exact one_mem _
  obtain ⟨ρ, hρΘ, hρ3, hρE, hρb, hρnot, hρc⟩ := h2 G (thetaC c) E b c v v'
    (thetaC_not_dvd c) hEe hcE hY.hbE (fun x hx => hNΘ (hEC hx)) (hNΘ (hLC hvL)) (hNΘ hv'C)
    (h1Θ v hv3) (h1Θ v' hv'3) hcomm hEv hEv' hb hnot
  obtain ⟨hρL, hρI⟩ := h3 G A c L E F a b R Y hY v v' ρ hvL hv'C hL' hρ3 hρΘ
  exact ⟨ρ, ⟨hρ3, hρnot, hρb, hρE, hρL, hρI, hρc⟩⟩

@[expose] def S2a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (c : G) (L L' : Subgroup G),
    L ∈ thetaComponentsAt 3 c → L' ∈ thetaComponentsAt 3 c → L ≠ L' →
    ∀ l ∈ L, ∀ l' ∈ L', l * l' * l⁻¹ * l'⁻¹ ∈ thetaC c

@[expose] def S2swap : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E F : Subgroup G) (a b : G)
    (R Y : Subgroup G), YCfg G A c L E F a b R Y →
      ∀ (t : G) (EY : Subgroup G), InvData E b c Y t EY → t ∉ Subgroup.normalizer (L : Set G) →
        Subgroup.map (MulAut.conj t).toMonoidHom L ∈ thetaComponentsAt 3 c ∧
        Subgroup.map (MulAut.conj t).toMonoidHom L ≠ L ∧
        (∀ x ∈ E ⊓ L, t * x * t⁻¹ ∈ E ⊓ Sec4.thetaQuotCentralizer L) ∧
        (∀ x ∈ E ⊓ Sec4.thetaQuotCentralizer L, t * x * t⁻¹ ∈ E ⊓ L) ∧
        (∀ x ∈ E ⊓ Sec4.thetaQuotCentralizer L, t⁻¹ * x * t ∈ E ⊓ L)

@[expose] def S2fus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E : Subgroup G),
    Cfg G A c L E →
      ∃ v ∈ L, v ^ 3 = 1 ∧
        (∀ y ∈ E ⊓ Sec4.thetaQuotCentralizer L, v * y * v⁻¹ * y⁻¹ ∈ thetaC c) ∧
        (∀ y ∈ E ⊓ L, v * y * v⁻¹ * y⁻¹ ∈ Subgroup.zpowers c ⊔ thetaC c) ∧
        ∃ y ∈ E ⊓ L, v * y * v⁻¹ * y⁻¹ ∉ thetaC c

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
