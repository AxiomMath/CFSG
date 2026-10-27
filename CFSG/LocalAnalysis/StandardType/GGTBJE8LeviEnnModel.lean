module

public import CFSG.LocalAnalysis.StandardType.GGMaxRankJModel
public import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylNoLine
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLift
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

private theorem eq_one_of_mem_centralizer_of_center_eq_bot {G : Type} [Group G] {X : Subgroup G}
    (hX : Subgroup.center X = ⊥) {z : G} (hzX : z ∈ X)
    (hzC : z ∈ Subgroup.centralizer (X : Set G)) : z = 1 := by
  have hz : (⟨z, hzX⟩ : X) ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hzC (w : G) w.2
  rw [hX, Subgroup.mem_bot] at hz
  simpa using congrArg Subtype.val hz

private theorem eq_of_conj_eq_of_center_eq_bot {G : Type} [Group G] {X : Subgroup G}
    (hX : Subgroup.center X = ⊥) {u v : G} (huX : u ∈ X) (hvX : v ∈ X)
    (h : ∀ y ∈ X, u * y * u⁻¹ = v * y * v⁻¹) : u = v := by
  have huvX : u⁻¹ * v ∈ X := X.mul_mem (X.inv_mem huX) hvX
  have huvC : u⁻¹ * v ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    calc y * (u⁻¹ * v) = u⁻¹ * (u * y * u⁻¹) * v := by group
      _ = u⁻¹ * (v * y * v⁻¹) * v := by rw [h y hy]
      _ = (u⁻¹ * v) * y := by group
  have h1 : u⁻¹ * v = 1 := eq_one_of_mem_centralizer_of_center_eq_bot hX huvX huvC
  calc u = u * 1 := by group
    _ = u * (u⁻¹ * v) := by rw [h1]
    _ = v := by group

private theorem mem_centralizer_of_conj_action {G : Type} [Group G] {X : Subgroup G} {b x : G}
    (h : ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹) :
    x⁻¹ * b ∈ Subgroup.centralizer (X : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  calc y * (x⁻¹ * b) = x⁻¹ * (x * y * x⁻¹) * b := by group
    _ = x⁻¹ * (b * y * b⁻¹) * b := by rw [← h y hy]
    _ = (x⁻¹ * b) * y := by group

private theorem mem_bstar_of_conj_eq {G : Type} [Group G] {p : ℕ} {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hZX : Subgroup.center X = ⊥) (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {b x : G} (hb : b ∈ Bs) (hxX : x ∈ X)
    (hact : ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹) : x ∈ Bs := by
  have hcomm : x ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b' hb'
    have hb'X : b' ∈ Subgroup.normalizer (X : Set G) := hN hb'
    have hb'xX : b' * x * b'⁻¹ ∈ X :=
      ((Subgroup.mem_normalizer_iff.mp hb'X) x).mp hxX
    have hact' : ∀ y ∈ X, b' * x * b'⁻¹ * y * (b' * x * b'⁻¹)⁻¹ = x * y * x⁻¹ := by
      intro y hy
      have hb'iyX : b'⁻¹ * y * b' ∈ X := by
        simpa using ((Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer (X : Set G)).inv_mem hb'X)) y).mp hy
      calc b' * x * b'⁻¹ * y * (b' * x * b'⁻¹)⁻¹
          = b' * (x * (b'⁻¹ * y * b') * x⁻¹) * b'⁻¹ := by group
        _ = b' * (b * (b'⁻¹ * y * b') * b⁻¹) * b'⁻¹ := by rw [hact _ hb'iyX]
        _ = (b' * b * b'⁻¹) * y * (b' * b * b'⁻¹)⁻¹ := by group
        _ = b * y * b⁻¹ := by
              rw [CFSG.Open.IsElemAbelian.comm hBs hb' hb]
              group
        _ = x * y * x⁻¹ := hact y hy
    have hu_eq : b' * x * b'⁻¹ = x :=
      eq_of_conj_eq_of_center_eq_bot hZX hb'xX hxX hact'
    calc b' * x = (b' * x * b'⁻¹) * b' := by group
      _ = x * b' := by rw [hu_eq]
  have hcC : x⁻¹ * b ∈ Subgroup.centralizer (X : Set G) :=
    mem_centralizer_of_conj_action hact
  have hxc : Commute x (x⁻¹ * b) :=
    Subgroup.mem_centralizer_iff.mp hcC x hxX
  have hbp : b ^ p = 1 := hBs.2 b hb
  have hbp' : b ^ p = x ^ p * (x⁻¹ * b) ^ p := by
    rw [← hxc.mul_pow]
    congr 1
    group
  have hxbpC : x ^ p ∈ Subgroup.centralizer (X : Set G) := by
    have hmul : x ^ p * (x⁻¹ * b) ^ p = 1 := by rw [← hbp', hbp]
    rw [mul_eq_one_iff_eq_inv.mp hmul]
    exact (Subgroup.centralizer (X : Set G)).inv_mem
      ((Subgroup.centralizer (X : Set G)).pow_mem hcC p)
  have hxbp1 : x ^ p = 1 :=
    eq_one_of_mem_centralizer_of_center_eq_bot hZX (X.pow_mem hxX p) hxbpC
  exact hSC x hcomm hxbp1

private theorem ggEnn_conj_injective {R : Type} [Group R] (hZ : Subgroup.center R = ⊥) :
    Function.Injective (MulAut.conj : R →* MulAut R) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : g ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hx := congrArg (fun f : MulAut R => f x) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at hx
    calc x * g = (g * x * g⁻¹) * g := by rw [hx]
      _ = g * x := by group
  rw [hZ] at hc
  exact hc

theorem ggEnnAdjointModel {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {R : Type} [Group R] (e : ↥X ≃* R)
    (hZX : Subgroup.center X = ⊥)
    (hinner : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {r : ℕ} (hlb : p ^ r ≤ Nat.card (ggGamma X hN).range) :
    ∃ E : Subgroup R,
      IsElemAbelian p E ∧ p ^ r ≤ Nat.card E ∧
      (∀ g : R, (∀ c ∈ E, g * c = c * g) → g ^ p = 1 → g ∈ E) ∧
      (ggGamma X hN).range.map (MulAut.congr e).toMonoidHom =
        E.map (MulAut.conj : R →* MulAut R) := by
  classical
  have hZR : Subgroup.center R = ⊥ := by
    have h1 : (Subgroup.center ↥X).map (e : ↥X →* R) = Subgroup.center R :=
      Subgroup.map_center_eq e
    rw [← h1, hZX, Subgroup.map_bot]
  have hinj : Function.Injective (MulAut.conj : R →* MulAut R) :=
    ggEnn_conj_injective hZR
  let E : Subgroup (R) := (Bs.subgroupOf X).map e.toMonoidHom
  have hcongr_conj : ∀ x : ↥X,
      MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
    intro x
    ext y
    obtain ⟨z, rfl⟩ := e.surjective y
    simp [MulAut.congr_apply, MulAut.conj_apply]
  have hArange : (ggGamma X hN).range.map (MulAut.congr e).toMonoidHom =
      E.map (MulAut.conj : R →* MulAut (R)) := by
    apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      obtain ⟨b, rfl⟩ := ha
      obtain ⟨x, hxX, hxact⟩ := hinner b b.2
      have hxBs : x ∈ Bs := mem_bstar_of_conj_eq hBs hSC hZX hN b.2 hxX hxact
      have hxsub : (⟨x, hxX⟩ : ↥X) ∈ Bs.subgroupOf X := hxBs
      have hconj : ggGamma X hN b = MulAut.conj (⟨x, hxX⟩ : ↥X) := by
        ext y
        exact hxact y y.2
      have hmemE : e ⟨x, hxX⟩ ∈ E := Subgroup.mem_map_of_mem e.toMonoidHom hxsub
      have heq : MulAut.conj (e ⟨x, hxX⟩) =
          (MulAut.congr e).toMonoidHom (ggGamma X hN b) := by
        rw [hconj]
        exact (hcongr_conj _).symm
      rw [← heq]
      exact Subgroup.mem_map_of_mem _ hmemE
    · rintro _ ⟨c, hc, rfl⟩
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hc
      change MulAut.conj (e x) ∈ (ggGamma X hN).range.map (MulAut.congr e).toMonoidHom
      have hxBs : (x : G) ∈ Bs := hx
      have hconj : ggGamma X hN ⟨(x : G), hxBs⟩ = MulAut.conj x := by
        ext y
        rfl
      have heq : MulAut.conj (e x) =
          (MulAut.congr e).toMonoidHom (ggGamma X hN ⟨(x : G), hxBs⟩) := by
        rw [hconj]
        exact (hcongr_conj x).symm
      rw [heq]
      exact Subgroup.mem_map_of_mem _ ⟨⟨(x : G), hxBs⟩, rfl⟩
  have hEel : IsElemAbelian p E := (hBs.subgroupOf X).map e.toMonoidHom
  have hcardEq : Nat.card E = Nat.card (ggGamma X hN).range := by
    have h2 : Nat.card ((ggGamma X hN).range.map (MulAut.congr e).toMonoidHom) =
        Nat.card (ggGamma X hN).range :=
      Subgroup.card_map_of_injective (MulAut.congr e).injective
    have h3 : Nat.card (E.map (MulAut.conj :
        R →* MulAut (R))) = Nat.card E :=
      Subgroup.card_map_of_injective hinj
    rw [← h3, ← h2, hArange]
  have hEcard : p ^ r ≤ Nat.card E := by
    rw [hcardEq]
    exact hlb
  have hEsc : ∀ g : R,
      (∀ c ∈ E, g * c = c * g) → g ^ p = 1 → g ∈ E := by
    intro g hgc hgp
    let z : ↥X := e.symm g
    have hzg : e z = g := e.apply_symm_apply g
    have hzC : (z : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨x, hxX, hxact⟩ := hinner b hb
      have hxBs : x ∈ Bs := mem_bstar_of_conj_eq hBs hSC hZX hN hb hxX hxact
      have hEx : e ⟨x, hxX⟩ ∈ E :=
        Subgroup.mem_map_of_mem e.toMonoidHom (show (⟨x, hxX⟩ : ↥X) ∈ Bs.subgroupOf X from hxBs)
      have hzx : z * (⟨x, hxX⟩ : ↥X) = ⟨x, hxX⟩ * z := by
        have h := hgc (e ⟨x, hxX⟩) hEx
        have h' : e.symm (g * e ⟨x, hxX⟩) = e.symm (e ⟨x, hxX⟩ * g) := by rw [h]
        simpa using h'
      have hzx' : (z : G) * x = x * (z : G) := congrArg Subtype.val hzx
      have hcb : x⁻¹ * b ∈ Subgroup.centralizer (X : Set G) :=
        mem_centralizer_of_conj_action hxact
      have hzc : (z : G) * (x⁻¹ * b) = (x⁻¹ * b) * (z : G) :=
        Subgroup.mem_centralizer_iff.mp hcb (z : G) z.2
      have hzxc : (z : G) * (x * (x⁻¹ * b)) = (x * (x⁻¹ * b)) * (z : G) := by
        calc (z : G) * (x * (x⁻¹ * b)) = ((z : G) * x) * (x⁻¹ * b) := by group
          _ = (x * (z : G)) * (x⁻¹ * b) := by rw [hzx']
          _ = x * ((z : G) * (x⁻¹ * b)) := by group
          _ = x * ((x⁻¹ * b) * (z : G)) := by rw [hzc]
          _ = (x * (x⁻¹ * b)) * (z : G) := by group
      have hbEq : (b : G) = x * (x⁻¹ * b) := by group
      rw [hbEq]
      exact hzxc.symm
    have hzpX : z ^ p = 1 := by
      apply e.injective
      rw [map_pow, hzg, hgp, map_one]
    have hzp : (z : G) ^ p = 1 := by
      simpa using congrArg Subtype.val hzpX
    have hzBs : (z : G) ∈ Bs := hSC z hzC hzp
    have hEz : g ∈ E := by
      rw [← hzg]
      exact Subgroup.mem_map_of_mem e.toMonoidHom (show z ∈ Bs.subgroupOf X from hzBs)
    exact hEz
  exact ⟨E, hEel, hEcard, hEsc, hArange⟩

theorem e8Enn_adjointModel
    {τ : Tag} {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {Fq : Type} [Field Fq] [Finite Fq] (e : ↥X ≃* adjointGroup τ Fq)
    (hZX : Subgroup.center X = ⊥)
    (hinner : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {r : ℕ} (hlb : p ^ r ≤ Nat.card (ggGamma X hN).range) :
    ∃ E : Subgroup (adjointGroup τ Fq),
      IsElemAbelian p E ∧ p ^ r ≤ Nat.card E ∧
      (∀ g : adjointGroup τ Fq, (∀ c ∈ E, g * c = c * g) → g ^ p = 1 → g ∈ E) ∧
      (ggGamma X hN).range.map (MulAut.congr e).toMonoidHom =
        E.map (MulAut.conj : adjointGroup τ Fq →* MulAut (adjointGroup τ Fq)) := by
  exact ggEnnAdjointModel hBs hSC e hZX hinner hN hlb

theorem ggE8Enn_model_L
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.E8, 0, n⟩ : LargeEvenLabel))
    (hL : GGHasLabel (⟨.E8, 0, n⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L))
    (hpn : p ∣ 2 ^ n + 1) :
    ∃ (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (Fq : Type) (_ : Field Fq) (_ : Finite Fq)
      (_ : CharP Fq 2), Nat.card Fq = 2 ^ n ∧
      ∃ (e : ↥L ≃* adjointGroup .E8 Fq) (E : Subgroup (adjointGroup .E8 Fq)),
        IsElemAbelian p E ∧ p ^ 7 ≤ Nat.card E ∧
        (∀ g : adjointGroup .E8 Fq, (∀ c ∈ E, g * c = c * g) → g ^ p = 1 → g ∈ E) ∧
        (ggGamma L hN).range.map (MulAut.congr e).toMonoidHom =
          E.map (MulAut.conj : adjointGroup .E8 Fq →* MulAut (adjointGroup .E8 Fq)) := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hn : 1 ≤ n := hΛ.1
    have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega]
      rw [pow_succ']
    rw [hpow] at hpn
    omega
  have hml : LargeEvenMarking ↥L (fun _ _ _ I _ θ => Bs ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :=
    hH.2.2.1.1
  obtain ⟨hLperf, _lab', R, _instR, _I, _F, θ, _hlab', hmark⟩ :=
    largeEvenMarking_exists' hml
  obtain ⟨hNmark, _hind⟩ := hmark
  obtain ⟨R₀, _instR₀, _finR₀, _hR₀card, ⟨⟨θ₀⟩, hlift₀⟩⟩ :=
    (largeEvenLabelAll_torusLift_excPlus (p := p) (lab := (⟨.E8, 0, n⟩ : LargeEvenLabel))
      hp hp2 ⟨Or.inr (Or.inl rfl), hpn⟩) _ hL
  have hlift : GGTorusLift p 7 R :=
    TableBF4.ggTorusLift_of_mulEquiv (θ.symm.trans θ₀) hlift₀
  have hlb : p ^ 7 ≤ Nat.card (ggGamma L hNmark).range :=
    (card_range_ggGamma_bstar_ge hH.1 hLperf θ hNmark hlift).1
  obtain ⟨Fq, _instFq, _instFin, _instChar, hFqcard, e, hZL, _hN', hinner⟩ :=
    ggMaxRank_model hRig hΛ hH.2.2.1.1 hL
  obtain ⟨E, hEel, hEcard, hEsc, hArange⟩ :=
    e8Enn_adjointModel hH.1.2.1.2.1 hH.1.2.1.2.2.2 e hZL hinner hNmark hlb
  exact ⟨hNmark, Fq, inferInstance, inferInstance, inferInstance, hFqcard, e, E,
    hEel, hEcard, hEsc, hArange⟩

theorem ggE8Enn_model_K
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.E8, 0, n⟩ : LargeEvenLabel))
    (hK : GGHasLabel (⟨.E8, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (hpn : p ∣ 2 ^ n + 1) :
    ∃ (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (Fq : Type) (_ : Field Fq) (_ : Finite Fq)
      (_ : CharP Fq 2), Nat.card Fq = 2 ^ n ∧
      ∃ (e : ↥K ≃* adjointGroup .E8 Fq) (E : Subgroup (adjointGroup .E8 Fq)),
        IsElemAbelian p E ∧ p ^ 7 ≤ Nat.card E ∧
        (∀ g : adjointGroup .E8 Fq, (∀ c ∈ E, g * c = c * g) → g ^ p = 1 → g ∈ E) ∧
        (ggGamma K hN).range.map (MulAut.congr e).toMonoidHom =
          E.map (MulAut.conj : adjointGroup .E8 Fq →* MulAut (adjointGroup .E8 Fq)) := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hn : 1 ≤ n := hΛ.1
    have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega]
      rw [pow_succ']
    rw [hpow] at hpn
    omega
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hmk : LargeEvenMarking ↥K (fun _ _ _ I _ θ => Bs ≤ Subgroup.normalizer (K : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :=
    hH.2.2.1.2 y K hnb
  obtain ⟨hKperf, _lab', R, _instR, _I, _F, θ, _hlab', hmark⟩ :=
    largeEvenMarking_exists' hmk
  obtain ⟨hNmark, _hind⟩ := hmark
  obtain ⟨R₀, _instR₀, _finR₀, _hR₀card, ⟨⟨θ₀⟩, hlift₀⟩⟩ :=
    (largeEvenLabelAll_torusLift_excPlus (p := p) (lab := (⟨.E8, 0, n⟩ : LargeEvenLabel))
      hp hp2 ⟨Or.inr (Or.inl rfl), hpn⟩) _ hK
  have hlift : GGTorusLift p 7 R :=
    TableBF4.ggTorusLift_of_mulEquiv (θ.symm.trans θ₀) hlift₀
  have hlb : p ^ 7 ≤ Nat.card (ggGamma K hNmark).range :=
    pow_le_card_range_ggGamma_bstar_of_torusLift hH.1 hnb hKperf θ hNmark hlift
  obtain ⟨Fq, _instFq, _instFin, _instChar, hFqcard, e, hZL, _hN', hinner⟩ :=
    ggMaxRank_model hRig hΛ (hH.2.2.1.2 y K hnb) hK
  obtain ⟨E, hEel, hEcard, hEsc, hArange⟩ :=
    e8Enn_adjointModel hH.1.2.1.2.1 hH.1.2.1.2.2.2 e hZL hinner hNmark hlb
  exact ⟨hNmark, Fq, inferInstance, inferInstance, inferInstance, hFqcard, e, E,
    hEel, hEcard, hEsc, hArange⟩

theorem ggEnnBstar {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) {R : Type} [Group R]
    (hZR : Subgroup.center R = ⊥) (e : ↥X ≃* R) {E : Subgroup R}
    (hA : (ggGamma X hN).range.map (MulAut.congr e).toMonoidHom =
      E.map (MulAut.conj : R →* MulAut R)) :
    ∃ ε : ↥Bs →* R,
      (∀ b, MulAut.congr e (ggGamma X hN b) = MulAut.conj (ε b)) ∧
      (∀ b, ε b ∈ E) ∧ (∀ c ∈ E, ∃ b, ε b = c) ∧
      (∀ b, ε b = 1 ↔ (b : G) ∈ Subgroup.centralizer (X : Set G)) ∧
      (∀ (b : ↥Bs) (hb : (b : G) ∈ X), ε b = e ⟨b, hb⟩) ∧
      (∀ b, ((e.symm (ε b) : ↥X) : G) ∈ Bs) ∧
      (∀ g : ↥X, e g ∈ Subgroup.normalizer (E : Set R) → (g : G) ∈ Subgroup.normalizer (Bs : Set G)) ∧
      (∀ g : ↥X, (g : G) ∈ Subgroup.normalizer (Bs : Set G) → e g ∈ Subgroup.normalizer (E : Set R)) ∧
      ∀ (g : ↥X) (b : ↥Bs) (hb : (g : G) * b * (g : G)⁻¹ ∈ Bs),
        ε ⟨_, hb⟩ = e g * ε b * (e g)⁻¹ := by
  classical
  have hZX : Subgroup.center X = ⊥ := center_eq_bot_of_mulEquiv e hZR
  have hinj : Function.Injective (MulAut.conj : R →* MulAut R) :=
    ggEnn_conj_injective hZR
  have hex : ∀ b : ↥Bs, ∃ c : R, c ∈ E ∧
      MulAut.congr e (ggGamma X hN b) = MulAut.conj c := by
    intro b
    have hb : MulAut.congr e (ggGamma X hN b) ∈
        E.map (MulAut.conj : R →* MulAut (R)) := by
      rw [← hA]
      exact Subgroup.mem_map_of_mem _ ⟨b, rfl⟩
    obtain ⟨c, hcE, hc⟩ := Subgroup.mem_map.mp hb
    exact ⟨c, hcE, hc.symm⟩
  let epsFun : ↥Bs → R := fun b => (hex b).choose
  have hspec : ∀ b, epsFun b ∈ E ∧
      MulAut.congr e (ggGamma X hN b) = MulAut.conj (epsFun b) := fun b => (hex b).choose_spec
  have huniq : ∀ (b : ↥Bs) (c : R), c ∈ E →
      MulAut.congr e (ggGamma X hN b) = MulAut.conj c → epsFun b = c := by
    intro b c _ hc
    exact hinj (by rw [← (hspec b).2, hc])
  have hone : epsFun 1 = 1 := by
    refine huniq 1 1 E.one_mem ?_
    simp only [map_one]
  have hmul : ∀ a b : ↥Bs, epsFun (a * b) = epsFun a * epsFun b := by
    intro a b
    refine huniq (a * b) (epsFun a * epsFun b) (E.mul_mem (hspec a).1 (hspec b).1) ?_
    simp only [map_mul, (hspec a).2, (hspec b).2]
  let eps : ↥Bs →* R :=
    { toFun := epsFun, map_one' := hone, map_mul' := hmul }
  have hspec' : ∀ b, eps b ∈ E ∧
      MulAut.congr e (ggGamma X hN b) = MulAut.conj (eps b) := hspec
  have honto : ∀ c ∈ E, ∃ b : ↥Bs, eps b = c := by
    intro c hcE
    have hcin : MulAut.conj c ∈
        (ggGamma X hN).range.map (MulAut.congr e).toMonoidHom := by
      rw [hA]
      exact Subgroup.mem_map_of_mem _ hcE
    obtain ⟨a, ha, haconj⟩ := Subgroup.mem_map.mp hcin
    obtain ⟨b, hb⟩ := ha
    refine ⟨b, ?_⟩
    apply hinj
    rw [← haconj, ← hb]
    exact ((hspec' b).2).symm
  have hker : ∀ b : ↥Bs, eps b = 1 ↔ (b : G) ∈ Subgroup.centralizer (X : Set G) := by
    intro b
    rw [← ggGamma_eq_one_iff X hN b]
    constructor
    · intro h
      apply (MulAut.congr e).injective
      rw [(hspec' b).2, h, map_one, map_one]
    · intro h
      apply hinj
      rw [← (hspec' b).2, h, map_one, map_one]
  have hact : ∀ (b : ↥Bs) (y : G), y ∈ X →
      (b : G) * y * (b : G)⁻¹ =
        ((e.symm (eps b) : ↥X) : G) * y * ((e.symm (eps b) : ↥X) : G)⁻¹ := by
    intro b y hy
    have hbyX : (b : G) * y * (b : G)⁻¹ ∈ X :=
      ((Subgroup.mem_normalizer_iff.mp (hN b.2)) y).mp hy
    have h1 : e (⟨(b : G) * y * (b : G)⁻¹, hbyX⟩ : ↥X) =
        eps b * e ⟨y, hy⟩ * (eps b)⁻¹ := by
      have h2 : e (ggGamma X hN b ⟨y, hy⟩) =
          (MulAut.congr e (ggGamma X hN b)) (e ⟨y, hy⟩) := by
        simp [MulAut.congr_apply]
      have h3 : (⟨(b : G) * y * (b : G)⁻¹, hbyX⟩ : ↥X) =
          ggGamma X hN b ⟨y, hy⟩ := Subtype.ext rfl
      rw [h3, h2, (hspec' b).2, MulAut.conj_apply]
    have h4 : (⟨(b : G) * y * (b : G)⁻¹, hbyX⟩ : ↥X) =
        e.symm (eps b) * ⟨y, hy⟩ * (e.symm (eps b))⁻¹ := by
      apply e.injective
      rw [h1, map_mul, map_mul, map_inv, e.apply_symm_apply]
    simpa using congrArg Subtype.val h4
  have hinner : ∀ (b : ↥Bs) (hb : (b : G) ∈ X), eps b = e ⟨b, hb⟩ := by
    intro b hb
    have hxb_eq : ((e.symm (eps b) : ↥X) : G) = (b : G) :=
      (eq_of_conj_eq_of_center_eq_bot hZX hb ((e.symm (eps b)).2) (hact b)).symm
    have hsub : e.symm (eps b) = (⟨b, hb⟩ : ↥X) := Subtype.ext hxb_eq
    calc eps b = e (e.symm (eps b)) := (e.apply_symm_apply (eps b)).symm
      _ = e ⟨b, hb⟩ := by rw [hsub]
  have hcentral : ∀ b : ↥Bs,
      ((e.symm (eps b) : ↥X) : G) ∈ Subgroup.centralizer (Bs : Set G) := by
    intro b
    rw [Subgroup.mem_centralizer_iff]
    intro b' hb'
    have hbX : ((e.symm (eps b) : ↥X) : G) ∈ X := (e.symm (eps b)).2
    have hb'X : (b' : G) ∈ Subgroup.normalizer (X : Set G) := hN hb'
    have huX : (b' : G) * ((e.symm (eps b) : ↥X) : G) * (b' : G)⁻¹ ∈ X :=
      ((Subgroup.mem_normalizer_iff.mp hb'X) ((e.symm (eps b) : ↥X) : G)).mp hbX
    have hact' : ∀ y ∈ X,
        (b' : G) * ((e.symm (eps b) : ↥X) : G) * (b' : G)⁻¹ * y *
          ((b' : G) * ((e.symm (eps b) : ↥X) : G) * (b' : G)⁻¹)⁻¹ =
        ((e.symm (eps b) : ↥X) : G) * y * ((e.symm (eps b) : ↥X) : G)⁻¹ := by
      intro y hy
      have hb'iyX : (b' : G)⁻¹ * y * (b' : G) ∈ X := by
        simpa using ((Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer (X : Set G)).inv_mem hb'X)) y).mp hy
      calc (b' : G) * ((e.symm (eps b) : ↥X) : G) * (b' : G)⁻¹ * y *
            ((b' : G) * ((e.symm (eps b) : ↥X) : G) * (b' : G)⁻¹)⁻¹
          = (b' : G) * (((e.symm (eps b) : ↥X) : G) * ((b' : G)⁻¹ * y * (b' : G)) *
              ((e.symm (eps b) : ↥X) : G)⁻¹) * (b' : G)⁻¹ := by group
        _ = (b' : G) * ((b : G) * ((b' : G)⁻¹ * y * (b' : G)) * (b : G)⁻¹) *
              (b' : G)⁻¹ := by rw [hact b _ hb'iyX]
        _ = ((b' : G) * (b : G) * (b' : G)⁻¹) * y *
              ((b' : G) * (b : G) * (b' : G)⁻¹)⁻¹ := by group
        _ = (b : G) * y * (b : G)⁻¹ := by
            rw [CFSG.Open.IsElemAbelian.comm hBs hb' b.2]
            group
        _ = ((e.symm (eps b) : ↥X) : G) * y * ((e.symm (eps b) : ↥X) : G)⁻¹ :=
            hact b y hy
    have hu_eq : (b' : G) * ((e.symm (eps b) : ↥X) : G) * (b' : G)⁻¹ =
        ((e.symm (eps b) : ↥X) : G) :=
      eq_of_conj_eq_of_center_eq_bot hZX huX hbX hact'
    calc (b' : G) * ((e.symm (eps b) : ↥X) : G)
        = ((b' : G) * ((e.symm (eps b) : ↥X) : G) * (b' : G)⁻¹) * (b' : G) := by group
      _ = ((e.symm (eps b) : ↥X) : G) * (b' : G) := by rw [hu_eq]
  have hmem : ∀ b : ↥Bs, ((e.symm (eps b) : ↥X) : G) ∈ Bs := by
    intro b
    have hbX : ((e.symm (eps b) : ↥X) : G) ∈ X := (e.symm (eps b)).2
    have hcC : ((e.symm (eps b) : ↥X) : G)⁻¹ * (b : G) ∈
        Subgroup.centralizer (X : Set G) :=
      mem_centralizer_of_conj_action (hact b)
    have hxc : Commute ((e.symm (eps b) : ↥X) : G)
        (((e.symm (eps b) : ↥X) : G)⁻¹ * (b : G)) :=
      Subgroup.mem_centralizer_iff.mp hcC ((e.symm (eps b) : ↥X) : G) hbX
    have hbp : (b : G) ^ p = 1 := hBs.2 b b.2
    have hbp' : (b : G) ^ p = ((e.symm (eps b) : ↥X) : G) ^ p *
        (((e.symm (eps b) : ↥X) : G)⁻¹ * (b : G)) ^ p := by
      rw [← hxc.mul_pow]
      congr 1
      group
    have hxbpC : ((e.symm (eps b) : ↥X) : G) ^ p ∈
        Subgroup.centralizer (X : Set G) := by
      have hmul : ((e.symm (eps b) : ↥X) : G) ^ p *
          (((e.symm (eps b) : ↥X) : G)⁻¹ * (b : G)) ^ p = 1 := by
        rw [← hbp', hbp]
      rw [mul_eq_one_iff_eq_inv.mp hmul]
      exact (Subgroup.centralizer (X : Set G)).inv_mem
        ((Subgroup.centralizer (X : Set G)).pow_mem hcC p)
    have hxbp1 : ((e.symm (eps b) : ↥X) : G) ^ p = 1 :=
      eq_one_of_mem_centralizer_of_center_eq_bot hZX (X.pow_mem hbX p) hxbpC
    exact hSC _ (hcentral b) hxbp1
  have hequiv : ∀ (g : ↥X) (b : ↥Bs) (hb : (g : G) * (b : G) * (g : G)⁻¹ ∈ Bs),
      eps ⟨_, hb⟩ = e g * eps b * (e g)⁻¹ := by
    intro g b hb
    apply hinj
    have hgg : ggGamma X hN ⟨_, hb⟩ =
        MulAut.conj g * ggGamma X hN b * MulAut.conj g⁻¹ := by
      ext y
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, ggGamma_coe]
      group
    have hconj : MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
      ext y
      obtain ⟨z, rfl⟩ := e.surjective y
      simp [MulAut.congr_apply]
    have hconj' : MulAut.congr e (MulAut.conj g⁻¹) = MulAut.conj ((e g)⁻¹) := by
      ext y
      obtain ⟨z, rfl⟩ := e.surjective y
      simp [MulAut.congr_apply]
    calc MulAut.conj (eps ⟨_, hb⟩)
        = MulAut.congr e (ggGamma X hN ⟨_, hb⟩) := ((hspec' _).2).symm
      _ = MulAut.congr e (MulAut.conj g * ggGamma X hN b * MulAut.conj g⁻¹) := by rw [hgg]
      _ = MulAut.conj (e g) * MulAut.conj (eps b) * MulAut.conj ((e g)⁻¹) := by
            rw [map_mul, map_mul, hconj, (hspec' b).2, hconj']
      _ = MulAut.conj (e g * eps b * (e g)⁻¹) := by
            simp only [map_mul, map_inv]
  have heE : ∀ z : ↥X, e z ∈ E → (z : G) ∈ Bs := by
    intro z hz
    obtain ⟨b, hb⟩ := honto (e z) hz
    have hz' : z = e.symm (eps b) := by
      rw [hb]
      exact (e.symm_apply_apply z).symm
    rw [hz']
    exact hmem b
  have hconj_mem : ∀ (h : ↥X), e h ∈ Subgroup.normalizer (E : Set (R)) →
      ∀ b : ↥Bs, (h : G) * (b : G) * (h : G)⁻¹ ∈ Bs := by
    intro h hhE b
    have hxbX : ((e.symm (eps b) : ↥X) : G) ∈ X := (e.symm (eps b)).2
    have hhxbX : (h : G) * ((e.symm (eps b) : ↥X) : G) * (h : G)⁻¹ ∈ X :=
      X.mul_mem (X.mul_mem h.2 hxbX) (X.inv_mem h.2)
    have hhxbE : e (⟨(h : G) * ((e.symm (eps b) : ↥X) : G) * (h : G)⁻¹, hhxbX⟩ : ↥X) ∈ E := by
      have h1 : (⟨(h : G) * ((e.symm (eps b) : ↥X) : G) * (h : G)⁻¹, hhxbX⟩ : ↥X) =
          h * e.symm (eps b) * h⁻¹ := Subtype.ext rfl
      rw [h1, map_mul, map_mul, map_inv, e.apply_symm_apply]
      exact ((Subgroup.mem_normalizer_iff.mp hhE) (eps b)).mp ((hspec' b).1)
    have hhxbBs : (h : G) * ((e.symm (eps b) : ↥X) : G) * (h : G)⁻¹ ∈ Bs :=
      heE ⟨_, hhxbX⟩ hhxbE
    have hcC : ((e.symm (eps b) : ↥X) : G)⁻¹ * (b : G) ∈
        Subgroup.centralizer (X : Set G) :=
      mem_centralizer_of_conj_action (hact b)
    have hcBs : ((e.symm (eps b) : ↥X) : G)⁻¹ * (b : G) ∈ Bs :=
      Bs.mul_mem (Bs.inv_mem (hmem b)) b.2
    have hfinal : (h : G) * (b : G) * (h : G)⁻¹ =
        ((h : G) * ((e.symm (eps b) : ↥X) : G) * (h : G)⁻¹) *
          (((e.symm (eps b) : ↥X) : G)⁻¹ * (b : G)) := by
      set c : G := ((e.symm (eps b) : ↥X) : G)⁻¹ * (b : G) with hc
      have hbEq : (b : G) = ((e.symm (eps b) : ↥X) : G) * c := by rw [hc]; group
      have hcComm : (h : G) * c = c * (h : G) := by
        rw [hc]
        exact Subgroup.mem_centralizer_iff.mp hcC (h : G) h.2
      rw [hbEq]
      have hch : (h : G) * c * (h : G)⁻¹ = c := by rw [hcComm]; group
      calc (h : G) * (((e.symm (eps b) : ↥X) : G) * c) * (h : G)⁻¹
          = ((h : G) * ((e.symm (eps b) : ↥X) : G) * (h : G)⁻¹) * ((h : G) * c * (h : G)⁻¹) := by
              group
        _ = ((h : G) * ((e.symm (eps b) : ↥X) : G) * (h : G)⁻¹) * c := by rw [hch]
    rw [hfinal]
    exact Bs.mul_mem hhxbBs hcBs
  have hnorm1 : ∀ g : ↥X, e g ∈ Subgroup.normalizer (E : Set (R)) →
      (g : G) ∈ Subgroup.normalizer (Bs : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact hconj_mem g hg ⟨y, hy⟩
    · intro hy
      have hg' : e (g⁻¹) ∈ Subgroup.normalizer (E : Set (R)) := by
        rw [map_inv]
        exact (Subgroup.normalizer (E : Set (R))).inv_mem hg
      have h1 := hconj_mem g⁻¹ hg' ⟨(g : G) * y * (g : G)⁻¹, hy⟩
      have h2 : ((g⁻¹ : ↥X) : G) = (g : G)⁻¹ := rfl
      rw [h2] at h1
      have h3 : (g : G)⁻¹ * ((g : G) * y * (g : G)⁻¹) * ((g : G)⁻¹)⁻¹ = y := by group
      rwa [h3] at h1
  have hfwd : ∀ (h : ↥X), (h : G) ∈ Subgroup.normalizer (Bs : Set G) →
      ∀ c ∈ E, e h * c * (e h)⁻¹ ∈ E := by
    intro h hh c hc
    obtain ⟨b, hb⟩ := honto c hc
    have hbBs : (h : G) * (b : G) * (h : G)⁻¹ ∈ Bs :=
      ((Subgroup.mem_normalizer_iff.mp hh) (b : G)).mp b.2
    rw [← hb, ← hequiv h b hbBs]
    exact (hspec' ⟨_, hbBs⟩).1
  have hnorm2 : ∀ g : ↥X, (g : G) ∈ Subgroup.normalizer (Bs : Set G) →
      e g ∈ Subgroup.normalizer (E : Set (R)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      exact hfwd g hg c hc
    · intro hc
      have hg' : ((g⁻¹ : ↥X) : G) ∈ Subgroup.normalizer (Bs : Set G) := by
        have := (Subgroup.normalizer (Bs : Set G)).inv_mem hg
        simpa using this
      have h1 := hfwd g⁻¹ hg' ((e g) * c * (e g)⁻¹) hc
      rw [show e (g⁻¹) = (e g)⁻¹ from map_inv e g] at h1
      have h2 : (e g)⁻¹ * ((e g) * c * (e g)⁻¹) * ((e g)⁻¹)⁻¹ = c := by group
      rwa [h2] at h1
  exact ⟨eps, (fun b => (hspec' b).2), (fun b => (hspec' b).1), honto, hker, hinner,
    hmem, hnorm1, hnorm2, hequiv⟩

theorem e8Enn_bstar
    {τ : Tag} {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) {K : Type} [Field K] [Finite K]
    (e : ↥X ≃* adjointGroup τ K) {E : Subgroup (adjointGroup τ K)}
    (hA : (ggGamma X hN).range.map (MulAut.congr e).toMonoidHom =
      E.map (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K))) :
    ∃ ε : ↥Bs →* adjointGroup τ K,
      (∀ b, MulAut.congr e (ggGamma X hN b) = MulAut.conj (ε b)) ∧
      (∀ b, ε b ∈ E) ∧ (∀ c ∈ E, ∃ b, ε b = c) ∧
      (∀ b, ε b = 1 ↔ (b : G) ∈ Subgroup.centralizer (X : Set G)) ∧
      (∀ (b : ↥Bs) (hb : (b : G) ∈ X), ε b = e ⟨b, hb⟩) ∧
      (∀ b, ((e.symm (ε b) : ↥X) : G) ∈ Bs) ∧
      (∀ g : ↥X, e g ∈ Subgroup.normalizer (E : Set (adjointGroup τ K)) →
        (g : G) ∈ Subgroup.normalizer (Bs : Set G)) ∧
      (∀ g : ↥X, (g : G) ∈ Subgroup.normalizer (Bs : Set G) →
        e g ∈ Subgroup.normalizer (E : Set (adjointGroup τ K))) ∧
      ∀ (g : ↥X) (b : ↥Bs) (hb : (g : G) * b * (g : G)⁻¹ ∈ Bs),
        ε ⟨_, hb⟩ = e g * ε b * (e g)⁻¹ := by
  exact ggEnnBstar hBs hSC hN center_adjointGroup_eq_bot e hA

end CFSG.StandardType

end
