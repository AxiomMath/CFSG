module

public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpDefs

public section

namespace CFSG.StandardType.GGKG3

open CFSG.Open

private def kg3_conjAutEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) :
    MulAut X ≃* MulAut Y where
  toFun σ := (e.symm.trans σ).trans e
  invFun τ := (e.trans τ).trans e.symm
  left_inv σ := by ext x; simp
  right_inv τ := by ext y; simp
  map_mul' σ τ := by ext y; simp [MulAut.mul_apply]

private theorem kg3_conjAutEquiv_apply {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (σ : MulAut X) (y : Y) : kg3_conjAutEquiv e σ y = e (σ (e.symm y)) := by
  simp [kg3_conjAutEquiv]

private theorem kg3_conjAutEquiv_apply_self {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (σ : MulAut X) (x : X) : kg3_conjAutEquiv e σ (e x) = e (σ x) := by
  rw [kg3_conjAutEquiv_apply, e.symm_apply_apply]

private theorem kg3_conjAutEquiv_isReflection {X Y : Type} [Group X] [Group Y]
    (P : Subgroup X) (P' : Subgroup Y) (θ : ↥P ≃* ↥P') (p : ℕ) (φ : MulAut ↥P) :
    GGIsReflection p φ ↔ GGIsReflection p (kg3_conjAutEquiv θ φ) := by
  have hfix : ∀ b : ↥P,
      (φ b = b) ↔ (kg3_conjAutEquiv θ φ (θ b) = θ b) := by
    intro b
    rw [kg3_conjAutEquiv_apply_self]
    exact ⟨fun h => congrArg θ h, fun h => θ.injective h⟩
  have hfix' : ∀ b' : ↥P',
      (kg3_conjAutEquiv θ φ b' = b') ↔ (φ (θ.symm b') = θ.symm b') := by
    intro b'
    have h := hfix (θ.symm b')
    rw [θ.apply_symm_apply] at h
    exact h.symm
  let eFix : {b : ↥P // φ b = b} ≃ {b' : ↥P' // kg3_conjAutEquiv θ φ b' = b'} :=
    { toFun := fun b => ⟨θ b.1, (hfix b.1).mp b.2⟩
      invFun := fun b' => ⟨θ.symm b'.1, (hfix' b'.1).mp b'.2⟩
      left_inv := by intro b; ext; simp
      right_inv := by intro b'; ext; simp }
  have hcard : Nat.card {b : ↥P // φ b = b}
      = Nat.card {b' : ↥P' // kg3_conjAutEquiv θ φ b' = b'} := Nat.card_congr eFix
  have hP : Nat.card ↥P = Nat.card ↥P' := Nat.card_congr θ.toEquiv
  constructor
  · rintro ⟨h2, hc⟩
    exact ⟨by rw [← map_pow, h2, map_one], by rw [← hcard, ← hP]; exact hc⟩
  · rintro ⟨h2, hc⟩
    exact ⟨by
      apply (kg3_conjAutEquiv θ).injective
      rw [map_pow, h2, map_one], by rw [hcard, hP]; exact hc⟩

private theorem kg3_transport_noRefl {G G' : Type} [Group G] [Group G'] (p : ℕ)
    (P : Subgroup G) (P' : Subgroup G') (H : Subgroup G) (H' : Subgroup G')
    (θ : ↥P ≃* ↥P')
    (hpart : ∀ g ∈ H, ∀ hg : g ∈ Subgroup.normalizer (P : Set G),
      ∃ g' ∈ H', ∃ hg' : g' ∈ Subgroup.normalizer (P' : Set G'),
        ∀ b : ↥P, θ (ggConjAut P hg b) = ggConjAut P' hg' (θ b))
    (h : ∀ φ ∈ ggAutomizer H' P', ¬ GGIsReflection p φ) :
    ∀ φ ∈ ggAutomizer H P, ¬ GGIsReflection p φ := by
  intro φ hφ hrefl
  obtain ⟨g, hgH, hgN, hφeq⟩ := mem_ggAutomizer_iff.mp hφ
  obtain ⟨g', hg'H, hg'N, hg'eq⟩ := hpart g hgH hgN
  have hmem : kg3_conjAutEquiv θ φ ∈ ggAutomizer H' P' := by
    rw [mem_ggAutomizer_iff]
    refine ⟨g', hg'H, hg'N, fun b => ?_⟩
    rw [kg3_conjAutEquiv_apply]
    have hφb : φ (θ.symm b) = ggConjAut P hgN (θ.symm b) := by
      apply Subtype.ext
      rw [hφeq (θ.symm b), ggConjAut_apply]
    rw [hφb]
    have hc := hg'eq (θ.symm b)
    rw [θ.apply_symm_apply] at hc
    rw [congrArg Subtype.val hc, ggConjAut_apply]
  exact h _ hmem ((kg3_conjAutEquiv_isReflection P P' θ p φ).mp hrefl)

theorem ggNoRefl_of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G') (P : Subgroup G)
    (h : ∀ φ ∈ ggAutomizer (⊤ : Subgroup G') (P.map e.toMonoidHom), ¬ GGIsReflection 7 φ) :
    ∀ φ ∈ ggAutomizer (⊤ : Subgroup G) P, ¬ GGIsReflection 7 φ := by
  refine kg3_transport_noRefl 7 P (P.map e.toMonoidHom) ⊤ ⊤ (e.subgroupMap P) ?_ h
  intro g _ hg
  have hg' : e g ∈ Subgroup.normalizer ((P.map e.toMonoidHom : Subgroup G') : Set G') := by
    rw [Subgroup.mem_normalizer_iff]
    intro h'
    constructor
    · intro hh'
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hh'
      refine Subgroup.mem_map.mpr
        ⟨g * b * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg b).mp hb, ?_⟩
      simp only [map_mul, map_inv]
      rfl
    · intro hh'
      obtain ⟨c, hc, hc'⟩ := Subgroup.mem_map.mp hh'
      refine Subgroup.mem_map.mpr ⟨g⁻¹ * c * g, ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * c * g)).mpr (by
          rwa [show g * (g⁻¹ * c * g) * g⁻¹ = c by group])
      · have h1 : e.toMonoidHom (g⁻¹ * c * g) = (e g)⁻¹ * e.toMonoidHom c * e g := by
          simp only [map_mul, map_inv]
          rfl
        rw [h1, hc']
        group
  refine ⟨e g, Subgroup.mem_top _, hg', ?_⟩
  intro b
  apply Subtype.ext
  change e (g * ↑b * g⁻¹) = e g * e ↑b * (e g)⁻¹
  simp only [map_mul, map_inv]

private theorem kg3_isInner_of_TB {R L' : Type} [Group R] [Group L']
    (ψ : L' →* R) (hψsurj : Function.Surjective ψ)
    (hkerZ : ψ.ker ≤ Subgroup.center L') (hcomm : commutator L' = ⊤)
    (I : Set (MulAut R)) (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R))
    (A : Subgroup (MulAut L'))
    (hAind : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) :
    A ≤ (MulAut.conj : L' →* MulAut L').range := by
  intro a ha
  obtain ⟨φa, hφaI, hφaeq⟩ := hAind a ha
  obtain ⟨ρ, hρ⟩ := hI hφaI
  obtain ⟨l, hl⟩ := hψsurj ρ
  subst hl
  refine ⟨l, ?_⟩
  set b : MulAut L' := (MulAut.conj l)⁻¹ * a with hb
  have hbψ : ∀ x : L', ψ (b x * x⁻¹) = 1 := by
    intro x
    have hx : ψ (b x) = ψ x := by
      have hbx : b x = l⁻¹ * a x * l := by
        have hb' : b = MulAut.conj l⁻¹ * a := by rw [hb, ← map_inv]
        rw [hb']
        simp only [MulAut.mul_apply, MulAut.conj_apply, inv_inv]
      rw [hbx, map_mul, map_mul, map_inv]
      have h1 : ψ (a x) = ψ l * ψ x * (ψ l)⁻¹ := by
        rw [← hφaeq x, ← hρ, MulAut.conj_apply]
      rw [h1]
      group
    rw [map_mul, map_inv, hx, mul_inv_cancel]
  have hcenter : ∀ x : L', b x * x⁻¹ ∈ Subgroup.center L' := fun x =>
    hkerZ (MonoidHom.mem_ker.mpr (hbψ x))
  let z : L' →* L' :=
    { toFun := fun x => b x * x⁻¹
      map_one' := by simp [hb, MulAut.mul_apply]
      map_mul' := by
        intro x y
        have hcy : x⁻¹ * (b y * y⁻¹) = (b y * y⁻¹) * x⁻¹ :=
          Subgroup.mem_center_iff.mp (hcenter y) x⁻¹
        show b (x * y) * (x * y)⁻¹ = (b x * x⁻¹) * (b y * y⁻¹)
        calc b (x * y) * (x * y)⁻¹
            = b x * (b y * y⁻¹) * x⁻¹ := by rw [map_mul, mul_inv_rev]; group
          _ = b x * (x⁻¹ * (b y * y⁻¹)) := by rw [hcy, mul_assoc]
          _ = (b x * x⁻¹) * (b y * y⁻¹) := by group }
  have hcommle : commutator L' ≤ z.ker := by
    change ⁅(⊤ : Subgroup L'), (⊤ : Subgroup L')⁆ ≤ z.ker
    rw [Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hcenter x) (z y)).symm
  have hz : z = 1 := by
    rw [← MonoidHom.ker_eq_top_iff]
    exact top_le_iff.mp (hcomm ▸ hcommle)
  have hb1 : b = 1 := by
    ext x
    have hx : b x * x⁻¹ = 1 := by
      have := congrArg (fun w : L' →* L' => w x) hz
      simpa [z] using this
    calc b x = b x * x⁻¹ * x := by group
      _ = 1 * x := by rw [hx]
      _ = x := one_mul x
  have : (MulAut.conj l)⁻¹ * a = 1 := by rw [← hb, hb1]
  rwa [inv_mul_eq_one] at this

private abbrev kg3_K {L' : Type} [Group L'] (A : Subgroup (MulAut L')) : Subgroup L' :=
  A.comap (MulAut.conj : L' →* MulAut L')

private abbrev kg3_abar {R L' : Type} [Group R] [Group L'] (ψ : L' →* R)
    (A : Subgroup (MulAut L')) : Subgroup R :=
  (A.comap (MulAut.conj : L' →* MulAut L')).map ψ

private theorem kg3_theta_exists {R L' : Type} [Group R] [Group L']
    (ψ : L' →* R) (hZker : ψ.ker = Subgroup.center L')
    (hconjZ : (MulAut.conj : L' →* MulAut L').ker = Subgroup.center L')
    (A : Subgroup (MulAut L'))
    (hinner : A ≤ (MulAut.conj : L' →* MulAut L').range) :
    ∃ θ : ↥A ≃* ↥(kg3_abar ψ A),
      ∀ (k : L') (hk : MulAut.conj k ∈ A),
        θ ⟨MulAut.conj k, hk⟩ =
          ⟨ψ k, Subgroup.mem_map_of_mem ψ (Subgroup.mem_comap.mpr hk)⟩ := by
  have hwd : ∀ l l' : L', MulAut.conj l = MulAut.conj l' → ψ l = ψ l' := by
    intro l l' h
    have hmem : l⁻¹ * l' ∈ Subgroup.center L' := by
      rw [← hconjZ, MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    have hψ : ψ (l⁻¹ * l') = 1 := by
      rw [← hZker, MonoidHom.mem_ker] at hmem
      exact hmem
    rw [map_mul, map_inv] at hψ
    rwa [inv_mul_eq_one] at hψ
  let choice : ∀ a : ↥A, L' := fun a => Classical.choose (hinner (x := a.1) a.2)
  have choice_spec : ∀ a : ↥A, MulAut.conj (choice a) = a.1 := fun a =>
    Classical.choose_spec (hinner (x := a.1) a.2)
  let θhom : ↥A →* ↥((A.comap (MulAut.conj : L' →* MulAut L')).map ψ) :=
    { toFun := fun a => ⟨ψ (choice a),
        Subgroup.mem_map_of_mem ψ (Subgroup.mem_comap.mpr (by rw [choice_spec a]; exact a.2))⟩
      map_one' := by
        apply Subtype.ext
        have h1mem : choice 1 ∈ Subgroup.center L' := by
          rw [← hconjZ, MonoidHom.mem_ker, choice_spec 1]
          rfl
        rw [← hZker, MonoidHom.mem_ker] at h1mem
        exact h1mem
      map_mul' := by
        intro a b
        apply Subtype.ext
        change ψ (choice (a * b)) = ψ (choice a) * ψ (choice b)
        rw [← map_mul]
        exact hwd (choice (a * b)) (choice a * choice b) (by
          rw [choice_spec (a * b), map_mul, choice_spec a, choice_spec b]
          rfl) }
  have hinj : Function.Injective θhom := by
    intro a b hab
    have hab' : ψ (choice a) = ψ (choice b) := congrArg Subtype.val hab
    have hmem : (choice a)⁻¹ * choice b ∈ Subgroup.center L' := by
      rw [← hZker, MonoidHom.mem_ker, map_mul, map_inv, hab', inv_mul_cancel]
    have hker : (choice a)⁻¹ * choice b ∈ (MulAut.conj : L' →* MulAut L').ker := by
      rw [hconjZ]; exact hmem
    rw [MonoidHom.mem_ker, map_mul, map_inv] at hker
    have hconj : MulAut.conj (choice a) = MulAut.conj (choice b) := by
      rwa [inv_mul_eq_one] at hker
    apply Subtype.ext
    rw [← choice_spec a, ← choice_spec b, hconj]
  have hsurj : Function.Surjective θhom := by
    intro y
    obtain ⟨k, hkK, hk⟩ := Subgroup.mem_map.mp y.2
    have hkA : MulAut.conj k ∈ A := by rwa [Subgroup.mem_comap] at hkK
    refine ⟨⟨MulAut.conj k, hkA⟩, ?_⟩
    apply Subtype.ext
    change ψ (choice ⟨MulAut.conj k, hkA⟩) = ↑y
    rw [← hk]
    exact hwd _ _ (by rw [choice_spec])
  refine ⟨MulEquiv.ofBijective θhom ⟨hinj, hsurj⟩, ?_⟩
  intro k hk
  apply Subtype.ext
  change ψ (choice ⟨MulAut.conj k, hk⟩) = ψ k
  exact hwd _ k (by rw [choice_spec])


theorem ggTorusNoRefl_of_sylow {R : Type} [Group R] (I : Set (MulAut R)) (r : ℕ)
    (hZ : Subgroup.center R = ⊥) (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R))
    (hR : 7 ^ (Nat.card R).factorization 7 = 7 ^ 3)
    (E₀ : Subgroup R) (hc : Nat.card E₀ = 7 ^ 3)
    (hN : ∀ φ ∈ ggAutomizer (⊤ : Subgroup R) E₀, ¬ GGIsReflection 7 φ) :
    GGTorusNoRefl 7 r R I := by
  intro L' instL' instFin ψ A hTB φ hφ hrefl
  obtain ⟨hψsurj, hkerZ, hcomm, hAabel, hAind, hr, h3, hSelf⟩ := hTB
  have hZker : ψ.ker = Subgroup.center L' := by
    apply le_antisymm hkerZ
    intro x hx
    rw [MonoidHom.mem_ker]
    have hxR : ψ x ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro ρ
      obtain ⟨l, rfl⟩ := hψsurj ρ
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx l]
    rw [hZ] at hxR
    exact Subgroup.mem_bot.mp hxR
  have hinner : A ≤ (MulAut.conj : L' →* MulAut L').range :=
    kg3_isInner_of_TB ψ hψsurj hkerZ hcomm I hI A hAind
  have hconjZ : (MulAut.conj : L' →* MulAut L').ker = Subgroup.center L' := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      have h := congrArg (fun f : MulAut L' => f y) (MonoidHom.mem_ker.mp hx)
      rw [MulAut.conj_apply, MulAut.one_apply] at h
      have h' : x * y = y * x := by
        calc x * y = (x * y * x⁻¹) * x := by group
          _ = y * x := by rw [h]
      exact h'.symm
    · intro x hx
      rw [MonoidHom.mem_ker]
      apply MulEquiv.ext
      intro y
      rw [MulAut.conj_apply, MulAut.one_apply]
      calc x * y * x⁻¹ = y * x * x⁻¹ := by rw [Subgroup.mem_center_iff.mp hx y]
        _ = y := by group
  obtain ⟨θ, hθ⟩ := kg3_theta_exists ψ hZker hconjZ A hinner
  have hRne : Nat.card R ≠ 0 := by
    intro h0
    rw [h0] at hR
    simp at hR
  haveI : Finite R := Nat.finite_of_card_ne_zero hRne
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hAbarP : IsPGroup 7 ↥(kg3_abar ψ A) := by
    intro x
    obtain ⟨k, hkK, hkx⟩ := Subgroup.mem_map.mp x.2
    have hkA : MulAut.conj k ∈ A := by rwa [Subgroup.mem_comap] at hkK
    have hk7 : ψ (k ^ 7) = 1 := by
      have hconj7 : MulAut.conj (k ^ 7) = 1 := by
        rw [map_pow, hAabel.2 (MulAut.conj k) hkA]
      have hmem : k ^ 7 ∈ Subgroup.center L' := by
        rw [← hconjZ, MonoidHom.mem_ker]; exact hconj7
      rw [← hZker, MonoidHom.mem_ker] at hmem
      exact hmem
    refine ⟨1, ?_⟩
    have hx7 : x ^ 7 = 1 := by
      apply Subtype.ext
      change (x : R) ^ 7 = 1
      rw [← hkx, ← map_pow, hk7]
    simpa using hx7
  obtain ⟨P, hAP⟩ := IsPGroup.exists_le_sylow hAbarP
  have hP_card : Nat.card ↥(P : Subgroup R) = 7 ^ 3 := by
    rw [Sylow.card_eq_multiplicity P, hR]
  have hAbar_le : Nat.card (kg3_abar ψ A) ≤ Nat.card ↥(P : Subgroup R) :=
    Nat.card_le_card_of_injective
      (fun x : ↥(kg3_abar ψ A) => (⟨x.1, hAP x.2⟩ : ↥(P : Subgroup R)))
      (by
        intro x y hxy
        apply Subtype.ext
        exact congrArg (fun z : ↥(P : Subgroup R) => z.1) hxy)
  have hAbar_ge : 7 ^ 3 ≤ Nat.card (kg3_abar ψ A) := by
    rw [← Nat.card_congr θ.toEquiv]
    exact h3
  have hAbarP_eq : kg3_abar ψ A = (P : Subgroup R) :=
    Subgroup.eq_of_le_of_card_ge hAP (by rw [hP_card]; exact hAbar_ge)
  have hE₀P : IsPGroup 7 ↥E₀ := IsPGroup.of_card (p := 7) (n := 3) hc
  obtain ⟨Q, hE₀Q⟩ := IsPGroup.exists_le_sylow hE₀P
  have hQ_card : Nat.card ↥(Q : Subgroup R) = 7 ^ 3 := by
    rw [Sylow.card_eq_multiplicity Q, hR]
  have hE₀Q_eq : E₀ = (Q : Subgroup R) :=
    Subgroup.eq_of_le_of_card_ge hE₀Q (by rw [hQ_card, hc])
  obtain ⟨ρ, hρ⟩ := MulAction.exists_smul_eq R Q P
  have hset : (↑(ρ • Q) : Subgroup R) = Q.map (MulAut.conj ρ).toMonoidHom := by
    apply Subgroup.ext
    intro x
    show x ∈ (↑(ρ • Q) : Set R) ↔ x ∈ (Q.map (MulAut.conj ρ).toMonoidHom : Set R)
    rw [Sylow.coe_smul]
    exact Set.mem_smul_set.trans (Iff.symm Subgroup.mem_map)
  have hρ_map : (P : Subgroup R) = Q.map (MulAut.conj ρ).toMonoidHom := by
    have h := congrArg (fun S : Sylow 7 R => (S : Subgroup R)) hρ
    rw [← h]
    exact hset
  have hρ_sub : kg3_abar ψ A = E₀.map (MulAut.conj ρ).toMonoidHom := by
    rw [hAbarP_eq, hE₀Q_eq, hρ_map]
  have hmap : (kg3_abar ψ A).map (MulAut.conj ρ⁻¹).toMonoidHom = E₀ := by
    rw [hρ_sub, Subgroup.map_map]
    have hcomp : (MulAut.conj ρ⁻¹).toMonoidHom.comp (MulAut.conj ρ).toMonoidHom
        = MonoidHom.id R := by
      ext x
      show MulAut.conj ρ⁻¹ (MulAut.conj ρ x) = x
      rw [MulAut.conj_apply, MulAut.conj_apply]
      group
    rw [hcomp]
    simp
  have hnoRefl : ∀ φ ∈ ggAutomizer (⊤ : Subgroup R) (kg3_abar ψ A),
      ¬ GGIsReflection 7 φ :=
    ggNoRefl_of_mulEquiv (MulAut.conj ρ⁻¹) (kg3_abar ψ A) (by rw [hmap]; exact hN)
  have hpart : ∀ g ∈ (MulAut.conj : L' →* MulAut L').range,
      ∀ hg : g ∈ Subgroup.normalizer (A : Set (MulAut L')),
        ∃ g' ∈ (⊤ : Subgroup R),
          ∃ hg' : g' ∈ Subgroup.normalizer (kg3_abar ψ A : Set R),
            ∀ b : ↥A, θ (ggConjAut A hg b) = ggConjAut (kg3_abar ψ A) hg' (θ b) := by
    intro g hg_range hgN
    obtain ⟨l, rfl⟩ := hg_range
    have hlK : l ∈ Subgroup.normalizer (kg3_K A : Set L') := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      rw [kg3_K, Subgroup.mem_comap, Subgroup.mem_comap]
      have hx : MulAut.conj (l * x * l⁻¹)
          = MulAut.conj l * MulAut.conj x * (MulAut.conj l)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      rw [hx]
      exact Subgroup.mem_normalizer_iff.mp hgN (MulAut.conj x)
    have hlAbarN : ψ l ∈ Subgroup.normalizer (kg3_abar ψ A : Set R) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      show y ∈ (kg3_K A).map ψ ↔ ψ l * y * (ψ l)⁻¹ ∈ (kg3_K A).map ψ
      constructor
      · intro hy
        obtain ⟨k, hkK, hky⟩ := Subgroup.mem_map.mp hy
        rw [← hky]
        have h1 : ψ l * ψ k * (ψ l)⁻¹ = ψ (l * k * l⁻¹) := by
          rw [map_mul, map_mul, map_inv]
        rw [h1]
        exact Subgroup.mem_map_of_mem ψ ((Subgroup.mem_normalizer_iff.mp hlK k).mp hkK)
      · intro hy
        obtain ⟨k, hkK, hky⟩ := Subgroup.mem_map.mp hy
        refine Subgroup.mem_map.mpr ⟨l⁻¹ * k * l, ?_, ?_⟩
        · exact (Subgroup.mem_normalizer_iff.mp hlK (l⁻¹ * k * l)).mpr (by
            rwa [show l * (l⁻¹ * k * l) * l⁻¹ = k by group])
        · have h1 : ψ (l⁻¹ * k * l) = (ψ l)⁻¹ * ψ k * ψ l := by
            rw [map_mul, map_mul, map_inv]
          rw [h1, hky]
          group
    refine ⟨ψ l, Subgroup.mem_top _, hlAbarN, fun b => ?_⟩
    obtain ⟨k, hk_eq⟩ := hinner (x := b.1) b.2
    have hmem : MulAut.conj (l * k * l⁻¹) ∈ A := by
      have h1 : MulAut.conj (l * k * l⁻¹)
          = MulAut.conj l * MulAut.conj k * (MulAut.conj l)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      rw [h1]
      exact (Subgroup.mem_normalizer_iff.mp hgN (MulAut.conj k)).mp (by
        rw [hk_eq]; exact b.2)
    have hbA : ggConjAut A hgN b = ⟨MulAut.conj (l * k * l⁻¹), hmem⟩ := by
      apply Subtype.ext
      rw [ggConjAut_apply, ← hk_eq]
      rw [show MulAut.conj l * MulAut.conj k * (MulAut.conj l)⁻¹
        = MulAut.conj (l * k * l⁻¹) by rw [map_mul, map_mul, map_inv]]
    have hkA : MulAut.conj k ∈ A := by rw [hk_eq]; exact b.2
    have hb : b = ⟨MulAut.conj k, hkA⟩ := Subtype.ext hk_eq.symm
    have hθb : θ b = ⟨ψ k, Subgroup.mem_map_of_mem ψ
        (Subgroup.mem_comap.mpr hkA)⟩ := by
      rw [congrArg θ hb, hθ k hkA]
    rw [hbA, hθ (l * k * l⁻¹) hmem, hθb]
    apply Subtype.ext
    rw [ggConjAut_apply]
    change ψ (l * k * l⁻¹) = ψ l * ψ k * (ψ l)⁻¹
    rw [map_mul, map_mul, map_inv]
  exact kg3_transport_noRefl 7 A (kg3_abar ψ A) (MulAut.conj : L' →* MulAut L').range ⊤ θ
    hpart hnoRefl φ hφ hrefl

end CFSG.StandardType.GGKG3
