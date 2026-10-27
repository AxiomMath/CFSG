module

public import CFSG.Quasithin.EmptyFaithful.ModHInn3
public import CFSG.Quasithin.EmptyFaithful.ModHCfg2
public import CFSG.Quasithin.EmptyFaithful.ModHNS

public section

namespace CFSG.Quasithin.ModH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem ker_rho0_le_kerPhi (c : CtxComp2 T Mc M V₁ V₂ Yp I L t)
    (hN : I ≤ Subgroup.normalizer (L : Set G))
    (hcen : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥) (hIeq : I = L ⊔ Sgp153 T V₁)
    (hYL : Yp ≤ L)
    (φ : ↥(Yp ⊔ Sgp153 T V₁) →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))
    (hφk : φ.ker = (oTwoPhi (Yp ⊔ Sgp153 T V₁)).subgroupOf (Yp ⊔ Sgp153 T V₁))
    (k : G) (hkH : k ∈ Yp ⊔ Sgp153 T V₁) (hk : k ∈ innerPart hN)
    (hk1 : rho0 hN hcen ⟨k, hk⟩ = 1) : φ ⟨k, hkH⟩ = 1 := by
  have hLI : L ≤ I := le_of_mem_cComp c.c33.mem
  have hSI := sgp153_le c
  have hHI : Yp ⊔ Sgp153 T V₁ ≤ I := sup_le (hYL.trans hLI) hSI
  have hker : IsPGroup 2 (rho0 hN hcen).ker := ker_rho0_isPGroup c hN hcen hIeq
  set ρ := rho0 hN hcen with hρ
  set Kg : Subgroup G := ρ.ker.map (innerPart hN).subtype with hKg
  have memKg : ∀ (x : G) (hx : x ∈ innerPart hN), x ∈ Kg ↔ ρ ⟨x, hx⟩ = 1 := by
    intro x hx
    constructor
    · rintro ⟨u, hu, hux⟩
      have : u = ⟨x, hx⟩ := Subtype.ext hux
      rw [this] at hu
      exact hu
    · intro h
      exact ⟨⟨x, hx⟩, h, rfl⟩
  have hKgp : IsPGroup 2 ↥Kg := by
    intro g
    obtain ⟨u, hu, hug⟩ := g.2
    obtain ⟨m, hm⟩ := hker ⟨u, hu⟩
    refine ⟨m, Subtype.ext ?_⟩
    have h1 := congrArg (fun z : ↥ρ.ker => (((z : ↥(innerPart hN)) : G))) hm
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h1
    have h2 : ((g : ↥Kg) : G) = (u : G) := hug.symm
    show ((g : G)) ^ (2 ^ m) = 1
    rw [h2]
    simpa using h1
  have hKgnorm : ∀ s ∈ I, ∀ x ∈ Kg, s * x * s⁻¹ ∈ Kg := by
    intro s hs x hx
    obtain ⟨u, hu, rfl⟩ := hx
    have hsx : s * (u : G) * s⁻¹ ∈ innerPart hN := innerPart_conj_mem hN hs u.2
    change s * (u : G) * s⁻¹ ∈ Kg
    rw [memKg _ hsx]
    have h2 := rho0_conj hN hcen ⟨s, hs⟩ u
    have hu1 : ρ u = 1 := hu
    have h3 : ρ ⟨s * (u : G) * s⁻¹, hsx⟩ = actQ hN ⟨s, hs⟩ (ρ u) := h2
    rw [h3, hu1, map_one]
  have hnorm : ((Kg ⊓ (Yp ⊔ Sgp153 T V₁)).subgroupOf (Yp ⊔ Sgp153 T V₁)).Normal := by
    refine ⟨fun x hx h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    refine ⟨?_, ?_⟩
    · have := hKgnorm (h : G) (hHI h.2) (x : G) hx.1
      simpa using this
    · exact (Yp ⊔ Sgp153 T V₁).mul_mem ((Yp ⊔ Sgp153 T V₁).mul_mem h.2 x.2)
        ((Yp ⊔ Sgp153 T V₁).inv_mem h.2)
  have hKhp : IsPGroup 2 ↥((Kg ⊓ (Yp ⊔ Sgp153 T V₁)).subgroupOf (Yp ⊔ Sgp153 T V₁)) :=
    isPGroup_subgroupOf (hKgp.to_inf_left)
  have hcore := CFSG.LieType.BorelTits.le_pCore 2 hnorm hKhp
  have hkK : (⟨k, hkH⟩ : ↥(Yp ⊔ Sgp153 T V₁)) ∈
      (Kg ⊓ (Yp ⊔ Sgp153 T V₁)).subgroupOf (Yp ⊔ Sgp153 T V₁) := by
    rw [Subgroup.mem_subgroupOf]
    exact ⟨(memKg k hk).2 hk1, hkH⟩
  have h1 : k ∈ pCoreOf 2 (Yp ⊔ Sgp153 T V₁) := ⟨⟨k, hkH⟩, hcore hkK, rfl⟩
  have h2 : (⟨k, hkH⟩ : ↥(Yp ⊔ Sgp153 T V₁)) ∈ φ.ker := by
    rw [hφk, Subgroup.mem_subgroupOf]
    exact SBd.pCoreOf_le_oTwoPhi _ h1
  exact h2

theorem exists_third (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) (hN : I ≤ Subgroup.normalizer (L : Set G))
    (hcen : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥) (hIeq : I = L ⊔ Sgp153 T V₁)
    (hYL : Yp ≤ L) :
    ∃ g : Subgroup (↥L ⧸ Subgroup.center ↥L),
      img (rho0 hN hcen) (Sgp153 T V₁) ≤ g ∧
      g ≤ img (rho0 hN hcen) Yp ⊔ img (rho0 hN hcen) (Sgp153 T V₁) ∧
      g ≠ img (rho0 hN hcen) Yp ⊔ img (rho0 hN hcen) (Sgp153 T V₁) ∧ 3 ∣ Nat.card ↥g ∧
      ∀ (s : G) (hs : s ∈ Sgp153 T V₁),
        g.map (actQ hN ⟨s, sgp153_le c hs⟩).toMonoidHom = g := by
  have hLI : L ≤ I := le_of_mem_cComp c.c33.mem
  have hSI := sgp153_le c
  have hYI : Yp ≤ I := hYL.trans hLI
  have hI0 : L ≤ innerPart hN := le_innerPart hN hLI
  have hYI0 : Yp ≤ innerPart hN := hYL.trans hI0
  have hSN := sgp153_le_normalizer_Yp c
  have hker : IsPGroup 2 (rho0 hN hcen).ker := ker_rho0_isPGroup c hN hcen hIeq
  have hHI : Yp ⊔ Sgp153 T V₁ ≤ I := sup_le hYI hSI
  have hS2 : IsPGroup 2 ↥(Sgp153 T V₁) := c.facts.sylow.2.1
  obtain ⟨φ, hφs, hφk⟩ := c.s3s3
  let φ₂ : ↥(Yp ⊔ Sgp153 T V₁) →* Equiv.Perm (Fin 3) := (MonoidHom.snd _ _).comp φ
  have hφ₂s : Function.Surjective φ₂ := by
    intro σ
    obtain ⟨h, hh⟩ := hφs (1, σ)
    exact ⟨h, by simp [φ₂, hh]⟩
  have hSyl : IsSylowTwoOf (Sgp153 T V₁) (Yp ⊔ Sgp153 T V₁) :=
    A4.isSylowTwoOf_mono c.facts.sylow le_sup_right hHI
  set SH : Subgroup ↥(Yp ⊔ Sgp153 T V₁) := (Sgp153 T V₁).subgroupOf (Yp ⊔ Sgp153 T V₁) with hSH
  set Tp : Subgroup (Equiv.Perm (Fin 3)) := SH.map φ₂ with hTp
  have hTp2 : IsPGroup 2 ↥Tp := by
    have h1 : IsPGroup 2 ↥SH := isPGroup_subgroupOf hS2
    exact h1.of_surjective (φ₂.subgroupMap SH) (φ₂.subgroupMap_surjective SH)
  have hcardP : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    rfl
  have hTpd : Nat.card ↥Tp ∣ 6 := hcardP ▸ Subgroup.card_subgroup_dvd_card Tp
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hTp2
  have hTbot : Tp ≠ ⊥ := by
    intro hb
    have hle : SH ≤ φ₂.ker := by
      intro x hx
      have : φ₂ x ∈ Tp := Subgroup.mem_map_of_mem _ hx
      rw [hb, Subgroup.mem_bot] at this
      exact this
    have h1 : φ₂.ker.index ∣ SH.index := Subgroup.index_dvd_of_le hle
    have h2 : φ₂.ker.index = 6 := by
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hφ₂s, Subgroup.card_top, hcardP]
    have h4 := hSyl.2.2
    rw [h2] at h1
    exact h4 ((show (2 : ℕ) ∣ 6 by norm_num).trans h1)
  have hTc : Nat.card ↥Tp = 2 := by
    have h1 : Nat.card ↥Tp ≠ 1 := fun h => hTbot (Subgroup.card_eq_one.1 h)
    rw [hn] at h1 hTpd ⊢
    have hn0 : n ≠ 0 := fun h => h1 (by rw [h]; rfl)
    have hn2 : n < 2 := by
      by_contra hcon
      have : 2 ^ 2 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
      have := this.trans hTpd
      omega
    have : n = 1 := by omega
    rw [this]
    rfl
  have hTntop : Tp ≠ ⊤ := by
    intro htop
    rw [htop, Subgroup.card_top, hcardP] at hTc
    omega
  set M₀ : Subgroup ↥(Yp ⊔ Sgp153 T V₁) := Tp.comap φ₂ with hM₀
  set Mg : Subgroup G := M₀.map (Yp ⊔ Sgp153 T V₁).subtype with hMg
  have memM : ∀ (x : G) (hx : x ∈ Yp ⊔ Sgp153 T V₁), x ∈ Mg ↔ φ₂ ⟨x, hx⟩ ∈ Tp := by
    intro x hx
    constructor
    · rintro ⟨u, hu, hux⟩
      have : u = ⟨x, hx⟩ := Subtype.ext hux
      rw [this] at hu
      exact hu
    · intro h
      exact ⟨⟨x, hx⟩, h, rfl⟩
  have memM' : ∀ x ∈ Mg, ∃ hx : x ∈ Yp ⊔ Sgp153 T V₁, φ₂ ⟨x, hx⟩ ∈ Tp := by
    rintro x ⟨u, hu, rfl⟩
    exact ⟨u.2, hu⟩
  have hMH : Mg ≤ Yp ⊔ Sgp153 T V₁ := fun x hx => (memM' x hx).1
  have hSM : Sgp153 T V₁ ≤ Mg := by
    intro s hs
    have hsH : s ∈ Yp ⊔ Sgp153 T V₁ := Subgroup.mem_sup_right hs
    rw [memM s hsH]
    exact Subgroup.mem_map_of_mem _ (show (⟨s, hsH⟩ : ↥(Yp ⊔ Sgp153 T V₁)) ∈ SH from hs)
  refine ⟨img (rho0 hN hcen) Mg, img_mono hSM, ?_, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨m, hmI0, hmM, rfl⟩ := mem_img.1 hq
    have hmH := hMH hmM
    obtain ⟨p, hp, s, hs, hms⟩ := ModG.Red.exists_mul_of_mem_sup' hSN hmH
    have hpI0 : p ∈ innerPart hN := hYI0 hp
    have hsI0 : s ∈ innerPart hN := by
      have : s = p⁻¹ * m := by rw [hms]; group
      rw [this]
      exact (innerPart hN).mul_mem ((innerPart hN).inv_mem hpI0) hmI0
    have e1 : (⟨m, hmI0⟩ : ↥(innerPart hN)) = ⟨p, hpI0⟩ * ⟨s, hsI0⟩ := Subtype.ext hms
    rw [e1, map_mul]
    exact Subgroup.mul_mem_sup (mem_img.2 ⟨p, hpI0, hp, rfl⟩) (mem_img.2 ⟨s, hsI0, hs, rfl⟩)
  · intro hgZ'
    have hYM : Yp ≤ Mg := by
      intro y hy
      have hyI0 := hYI0 hy
      have hyq : rho0 hN hcen ⟨y, hyI0⟩ ∈ img (rho0 hN hcen) Mg := by
        rw [hgZ']
        exact Subgroup.mem_sup_left (mem_img.2 ⟨y, hyI0, hy, rfl⟩)
      obtain ⟨m, hmI0, hmM, hmy⟩ := mem_img.1 hyq
      have hmH := hMH hmM
      have hyH : y ∈ Yp ⊔ Sgp153 T V₁ := Subgroup.mem_sup_left hy
      have hkH : m⁻¹ * y ∈ Yp ⊔ Sgp153 T V₁ :=
        (Yp ⊔ Sgp153 T V₁).mul_mem ((Yp ⊔ Sgp153 T V₁).inv_mem hmH) hyH
      have hkI0 : m⁻¹ * y ∈ innerPart hN :=
        (innerPart hN).mul_mem ((innerPart hN).inv_mem hmI0) hyI0
      have hk1 : rho0 hN hcen ⟨m⁻¹ * y, hkI0⟩ = 1 := by
        have e : (⟨m⁻¹ * y, hkI0⟩ : ↥(innerPart hN)) = ⟨m, hmI0⟩⁻¹ * ⟨y, hyI0⟩ := rfl
        rw [e, map_mul, map_inv, hmy, inv_mul_cancel]
      have hφk1 := ker_rho0_le_kerPhi c hN hcen hIeq hYL φ hφk (m⁻¹ * y) hkH hkI0 hk1
      have hkM : m⁻¹ * y ∈ Mg := by
        rw [memM _ hkH]
        have : φ₂ ⟨m⁻¹ * y, hkH⟩ = 1 := by simp [φ₂, hφk1]
        rw [this]
        exact Tp.one_mem
      have : y = m * (m⁻¹ * y) := by group
      rw [this]
      exact Mg.mul_mem hmM hkM
    have hHM : Yp ⊔ Sgp153 T V₁ ≤ Mg := sup_le hYM hSM
    apply hTntop
    rw [eq_top_iff]
    intro σ _
    obtain ⟨h, rfl⟩ := hφ₂s σ
    have := (memM h.1 h.2).1 (hHM h.2)
    simpa using this
  · obtain ⟨b, k, hk2, -, hcard⟩ := SBd11.card_form_of_struct c.facts11.struct_Yp
    let ψ : ↥Yp →* Equiv.Perm (Fin 3) := φ₂.comp (Subgroup.inclusion (le_sup_left : Yp ≤ Yp ⊔ Sgp153 T V₁))
    have hprod := Subgroup.card_ker_mul_card_range ψ
    have hrd : Nat.card ψ.range ∣ 6 := hcardP ▸ Subgroup.card_subgroup_dvd_card ψ.range
    have h1 : 9 ∣ Nat.card ψ.ker * Nat.card ψ.range := by
      have h9 : 9 ∣ 3 ^ k := (show (9 : ℕ) = 3 ^ 2 by norm_num) ▸ pow_dvd_pow 3 hk2
      refine h9.trans ?_
      rw [hprod, hcard]
      exact Dvd.intro_left _ rfl
    have h2 : 3 ∣ Nat.card ψ.ker := by
      have hr6 : Nat.card ψ.range ≤ 6 := Nat.le_of_dvd (by norm_num) hrd
      generalize Nat.card ψ.range = r at h1 hrd hr6
      generalize Nat.card ψ.ker = x at h1 ⊢
      interval_cases r <;> omega
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥ψ.ker) 3 h2
    set y₀ : ↥Yp := (y : ↥Yp) with hy₀
    have hy₀ord : orderOf y₀ = 3 := by rw [hy₀, Subgroup.orderOf_coe, hy]
    have hyk : ψ y₀ = 1 := y.2
    have hy₀H : y₀.1 ∈ Yp ⊔ Sgp153 T V₁ := Subgroup.mem_sup_left y₀.2
    have hy₀M : y₀.1 ∈ Mg := by
      rw [memM _ hy₀H]
      have : φ₂ ⟨y₀.1, hy₀H⟩ = 1 := hyk
      rw [this]
      exact Tp.one_mem
    have hy₀I0 : y₀.1 ∈ innerPart hN := hYI0 y₀.2
    set q := rho0 hN hcen ⟨y₀.1, hy₀I0⟩ with hq
    have hqg : q ∈ img (rho0 hN hcen) Mg := mem_img.2 ⟨y₀.1, hy₀I0, hy₀M, rfl⟩
    have hq3 : q ^ 3 = 1 := by
      rw [hq, ← map_pow]
      have : (⟨y₀.1, hy₀I0⟩ : ↥(innerPart hN)) ^ 3 = 1 := by
        apply Subtype.ext
        have h3 := congrArg (fun z : ↥Yp => ((z : ↥Yp) : G)) (hy₀ord ▸ pow_orderOf_eq_one y₀)
        simpa using h3
      rw [this, map_one]
    have hq1 : q ≠ 1 := by
      intro hq1
      have hmem : (⟨y₀.1, hy₀I0⟩ : ↥(innerPart hN)) ∈ (rho0 hN hcen).ker := hq1
      obtain ⟨m, hm⟩ := hker ⟨_, hmem⟩
      have h1' := congrArg (fun z : ↥(rho0 hN hcen).ker => (((z : ↥(innerPart hN)) : G))) hm
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at h1'
      have h2' : y₀ ^ (2 ^ m) = 1 := by
        apply Subtype.ext
        simpa using h1'
      have h3 : 3 ∣ 2 ^ m := hy₀ord ▸ orderOf_dvd_of_pow_eq_one h2'
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
    have hqord : orderOf q = 3 := by
      have hd : orderOf q ∣ 3 := orderOf_dvd_of_pow_eq_one hq3
      rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hq1
      · exact h
    have := orderOf_dvd_natCard (⟨q, hqg⟩ : ↥(img (rho0 hN hcen) Mg))
    rw [Subgroup.orderOf_mk, hqord] at this
    exact this
  · intro s hs
    have hsM : s ∈ Mg := hSM hs
    refine img_map_actQ hN hcen ⟨s, hSI hs⟩ (fun x => ⟨fun hx => ?_, fun hx => ?_⟩)
    · exact Mg.mul_mem (Mg.mul_mem hsM hx) (Mg.inv_mem hsM)
    · have := Mg.mul_mem (Mg.mul_mem (Mg.inv_mem hsM) hx) hsM
      simpa [mul_assoc] using this

theorem config2_of_ctx (c : CtxComp2 T Mc M V₁ V₂ Yp I L t)
    (hmin : ∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I)
    (hN : I ≤ Subgroup.normalizer (L : Set G))
    (hcen : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥) (hIeq : I = L ⊔ Sgp153 T V₁)
    (hYL : Yp ≤ L) :
    Config2 (↥L ⧸ Subgroup.center ↥L)
      {α | ∃ (s : G) (hs : s ∈ Sgp153 T V₁), α = actQ hN ⟨s, sgp153_le c hs⟩}
      (img (rho0 hN hcen) (Sgp153 T V₁)) (img (rho0 hN hcen) Yp) := by
  have hLI : L ≤ I := le_of_mem_cComp c.c33.mem
  have hSI := sgp153_le c
  have hSN := sgp153_le_normalizer_Yp c
  have hZ : centerOf L = CFSG.Open.pCoreOf 2 L := c.c33.center_eq
  have hpc := SBd13.pCore_eq_center_of_center_eq hZ
  have hker : IsPGroup 2 (rho0 hN hcen).ker := ker_rho0_isPGroup c hN hcen hIeq
  obtain ⟨g, hSg, hgZ, hgne, hg3, hig⟩ := exists_third c hN hcen hIeq hYL
  refine ⟨not_isSolvable_of_ctx c (QuotientGroup.quotientMulEquivOfEq hpc.symm).symm,
    isSylowTwoOf_img_S0 c hN hcen, img_le_normalizer_img hSN,
    (solvable_nine_img_Yp0 c hLI hYL hN hcen hker).1,
    (solvable_nine_img_Yp0 c hLI hYL hN hcen hker).2, ?_, ?_, ?_, ⟨g, hSg, hgZ, hgne, hg3, ?_⟩⟩
  · rintro α ⟨s, hs, rfl⟩
    exact img_map_actQ hN hcen ⟨s, hSI hs⟩ (fun x =>
      ⟨fun hx => (Sgp153 T V₁).mul_mem ((Sgp153 T V₁).mul_mem hs hx) ((Sgp153 T V₁).inv_mem hs),
        fun hx => by
          have := (Sgp153 T V₁).mul_mem ((Sgp153 T V₁).mul_mem ((Sgp153 T V₁).inv_mem hs) hx) hs
          simpa [mul_assoc] using this⟩)
  · rintro α ⟨s, hs, rfl⟩
    exact img_map_actQ hN hcen ⟨s, hSI hs⟩ (fun x => Subgroup.mem_normalizer_iff.1 (hSN hs) x)
  · intro N hNp hN1 hZN hinv hNtop
    exact hmin_prop0 c hmin hN hcen hIeq hYL N hNp hN1 hZN
      (fun s hs => hinv _ ⟨s, hs, rfl⟩) hNtop
  · rintro α ⟨s, hs, rfl⟩
    exact hig s hs

end CFSG.Quasithin.ModH
