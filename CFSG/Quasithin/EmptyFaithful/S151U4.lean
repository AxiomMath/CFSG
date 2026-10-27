module

public import CFSG.Quasithin.EmptyFaithful.S151U3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem s151u_orbit_fixed_le_one {X : Type*} [Group X] [Finite X] {Ω : Type*} [MulAction X Ω]
    [Finite Ω] (o : Ω) (ho : ∀ g : X, g • o = o) (B : Subgroup X) (hB2 : IsPGroup 2 B)
    (hno : ∀ ω : Ω, ω ≠ o → ∃ g : X, g • ω ≠ ω)
    (hsel : ∀ g ∈ Subgroup.normalizer (B : Set X), g ∈ B)
    (hmax : ∀ K : Subgroup X, B ≤ K → K ≠ ⊤ →
      ∃ H : Subgroup X, K ≤ H ∧ H ≠ ⊤ ∧ Nat.card H = 3 * Nat.card B)
    (hnum : Nat.card X = 3 * Nat.card B * (Nat.card Ω - 1)) :
    ∀ ω ω' : Ω, ω ≠ o → ω' ≠ o → (∀ b ∈ B, b • ω = ω) → (∀ b ∈ B, b • ω' = ω') → ω' = ω := by
  classical
  intro ω ω' hω hω' hBω hBω'
  have hBpos : 0 < Nat.card B := Nat.card_pos
  set St := MulAction.stabilizer X ω with hSt
  have hBSt : B ≤ St := fun b hb => hBω b hb
  have hStne : St ≠ ⊤ := by
    intro h
    obtain ⟨g, hg⟩ := hno ω hω
    exact hg (by
      have : g ∈ St := by rw [h]; trivial
      exact this)
  obtain ⟨H, hStH, hHne, hHcard⟩ := hmax St hBSt hStne
  have hidx : Nat.card (MulAction.orbit X ω) = St.index :=
    Nat.card_congr (MulAction.orbitEquivQuotientStabilizer X ω)
  have hcm : Nat.card St * St.index = Nat.card X := Subgroup.card_mul_index St
  have horbsub : MulAction.orbit X ω ⊆ ({o}ᶜ : Set Ω) := by
    rintro _ ⟨g, rfl⟩ h
    apply hω
    have h' : g • ω = o := h
    have : ω = g⁻¹ • o := by rw [← h']; simp
    rw [this, ho]
  have hcompl : (({o}ᶜ : Set Ω)).ncard = Nat.card Ω - 1 := by
    have := Set.ncard_compl ({o} : Set Ω)
    rw [Set.ncard_singleton] at this
    exact this
  have horb_le : Nat.card (MulAction.orbit X ω) ≤ Nat.card Ω - 1 := by
    rw [Nat.card_coe_set_eq]
    calc (MulAction.orbit X ω).ncard ≤ (({o}ᶜ : Set Ω)).ncard := Set.ncard_le_ncard horbsub
      _ = Nat.card Ω - 1 := hcompl
  have hΩ : 1 < Nat.card Ω := Finite.one_lt_card_iff_nontrivial.mpr ⟨⟨ω, o, hω⟩⟩
  have hm : 0 < Nat.card Ω - 1 := by omega
  have hStpos : 0 < Nat.card St := Nat.card_pos
  have hStle : Nat.card St ≤ Nat.card H := Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hStH)
  have h1 : Nat.card St * St.index ≤ Nat.card St * (Nat.card Ω - 1) := by
    apply Nat.mul_le_mul_left
    rw [← hidx]
    exact horb_le
  have h2 : Nat.card St * (Nat.card Ω - 1) ≤ Nat.card H * (Nat.card Ω - 1) :=
    Nat.mul_le_mul_right _ hStle
  have h3 : Nat.card H * (Nat.card Ω - 1) = Nat.card X := by
    rw [hHcard, hnum]
  have hStH_card : Nat.card St = Nat.card H := by
    have : Nat.card St * (Nat.card Ω - 1) = Nat.card H * (Nat.card Ω - 1) := by omega
    exact Nat.eq_of_mul_eq_mul_right hm this
  have hidx_eq : St.index = Nat.card Ω - 1 := by
    have : Nat.card St * St.index = Nat.card St * (Nat.card Ω - 1) := by omega
    exact Nat.eq_of_mul_eq_mul_left hStpos this
  have hStHeq : St = H := Subgroup.eq_of_le_of_card_ge hStH (le_of_eq hStH_card.symm)
  have hmem : ω' ∈ MulAction.orbit X ω := by
    by_contra hnot
    have hsub : MulAction.orbit X ω ⊆ (({o}ᶜ : Set Ω) \ {ω'}) := by
      intro x hx
      refine ⟨horbsub hx, ?_⟩
      intro hxe
      exact hnot (by rw [Set.mem_singleton_iff] at hxe; rw [← hxe]; exact hx)
    have hcard : (({o}ᶜ : Set Ω) \ {ω'}).ncard = Nat.card Ω - 1 - 1 := by
      rw [Set.ncard_sdiff_singleton_of_mem (by simpa using hω'), hcompl]
    have := Set.ncard_le_ncard hsub
    rw [hcard, ← Nat.card_coe_set_eq, hidx, hidx_eq] at this
    omega
  obtain ⟨g, hg⟩ := hmem
  have hstab : MulAction.stabilizer X ω' = St.map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    exact MulAction.stabilizer_smul_eq_stabilizer_map_conj g ω
  have hconj : ∀ b ∈ B, g⁻¹ * b * g ∈ H := by
    intro b hb
    have hb' : b ∈ MulAction.stabilizer X ω' := hBω' b hb
    rw [hstab] at hb'
    obtain ⟨y, hy, hyb⟩ := hb'
    have : g⁻¹ * b * g = y := by
      rw [← hyb]
      simp [MulAut.conj_apply, mul_assoc]
    rw [this, ← hStHeq]
    exact hy
  have hBH : B ≤ H := hBSt.trans hStH
  have hBind : ¬ 2 ∣ (B.subgroupOf H).index := by
    have h1 : Nat.card (B.subgroupOf H) * (B.subgroupOf H).index = Nat.card H :=
      Subgroup.card_mul_index _
    have h2 : Nat.card (B.subgroupOf H) = Nat.card B :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv
    rw [h2, hHcard] at h1
    have : (B.subgroupOf H).index = 3 := by
      have : Nat.card B * (B.subgroupOf H).index = Nat.card B * 3 := by rw [h1]; ring
      exact Nat.eq_of_mul_eq_mul_left hBpos this
    rw [this]
    omega
  let B' : Subgroup X := B.map (MulAut.conj g⁻¹).toMonoidHom
  have hB'2 : IsPGroup 2 B' := hB2.map _
  have hB'H : B' ≤ H := by
    rintro _ ⟨b, hb, rfl⟩
    have := hconj b hb
    simpa [MulAut.conj_apply, mul_assoc] using this
  obtain ⟨m', hm'H, hm'⟩ := CFSG.QuasithinUnique.EscapingLocal.exists_conj_mem_of_isPGroup hBH hB2 hBind hB'H hB'2
  have hcB : ∀ x ∈ B, (m' * g⁻¹) * x * (m' * g⁻¹)⁻¹ ∈ B := by
    intro x hx
    have := hm' (g⁻¹ * x * g) ⟨x, hx, by simp [mul_assoc]⟩
    simpa [mul_assoc] using this
  have hcnorm : (m' * g⁻¹) ∈ Subgroup.normalizer (B : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hcB x, fun hx => ?_⟩
    let Bc : Subgroup X := B.map (MulAut.conj (m' * g⁻¹)).toMonoidHom
    have hBcle : Bc ≤ B := by
      rintro _ ⟨b, hb, rfl⟩
      exact hcB b hb
    have hBccard : Nat.card B ≤ Nat.card Bc := by
      rw [Subgroup.card_map_of_injective (MulAut.conj (m' * g⁻¹)).injective]
    have hBceq : Bc = B := Subgroup.eq_of_le_of_card_ge hBcle hBccard
    have hxBc : (m' * g⁻¹) * x * (m' * g⁻¹)⁻¹ ∈ Bc := by rw [hBceq]; exact hx
    obtain ⟨b, hb, hbx⟩ := hxBc
    have : b = x := (MulAut.conj (m' * g⁻¹)).injective hbx
    rw [← this]
    exact hb
  have hcB' := hsel _ hcnorm
  have hgH : g ∈ H := by
    have : g = (m' * g⁻¹)⁻¹ * m' := by group
    rw [this]
    exact H.mul_mem (H.inv_mem (hBH hcB')) hm'H
  have hgSt : g ∈ St := by rw [hStHeq]; exact hgH
  have hg' : g • ω = ω' := hg
  have hgω : g • ω = ω := hgSt
  rw [← hg', hgω]

variable {G : Type} [Group G]

abbrev BlockN (L : Subgroup G) : Type := ↥(blockU L) ⧸ (blockZ L).subgroupOf (blockU L)

theorem s151u_conj_mem_U {L : Subgroup G} (l : ↥L) (u : ↥(blockU L)) :
    (l : G) * u * (l : G)⁻¹ ∈ blockU L :=
  (Subgroup.mem_normalizer_iff.mp (s151v_L_le_normalizer_blockU L l.2) u).mp u.2

@[expose] def s151uSmul (L : Subgroup G) (l : ↥L) : BlockN L → BlockN L :=
  Quotient.map' (fun u : ↥(blockU L) =>
      (⟨(l : G) * u * (l : G)⁻¹, s151u_conj_mem_U l u⟩ : ↥(blockU L)))
    (fun u u' h => by
      rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at h ⊢
      have hc := s151v_blockZ_comm h l.2
      show ((l : G) * (u : G) * (l : G)⁻¹)⁻¹ * ((l : G) * (u' : G) * (l : G)⁻¹) ∈ blockZ L
      have e : ((l : G) * (u : G) * (l : G)⁻¹)⁻¹ * ((l : G) * (u' : G) * (l : G)⁻¹) =
          (l : G) * ((u : G)⁻¹ * (u' : G)) * (l : G)⁻¹ := by group
      have hc' : (l : G) * ((u : G)⁻¹ * (u' : G)) * (l : G)⁻¹ = (u : G)⁻¹ * (u' : G) := hc
      rw [e, hc']
      exact h)

theorem s151uSmul_mk (L : Subgroup G) (l : ↥L) (u : ↥(blockU L)) :
    s151uSmul L l (u : BlockN L) =
      ((⟨(l : G) * u * (l : G)⁻¹, s151u_conj_mem_U l u⟩ : ↥(blockU L)) : BlockN L) := rfl

instance s151uAct (L : Subgroup G) : MulAction ↥L (BlockN L) where
  smul := s151uSmul L
  one_smul := fun x => by
    induction x using QuotientGroup.induction_on with
    | H u =>
      show s151uSmul L 1 (u : BlockN L) = u
      rw [s151uSmul_mk]
      congr 1
      apply Subtype.ext
      simp
  mul_smul := fun l m x => by
    induction x using QuotientGroup.induction_on with
    | H u =>
      show s151uSmul L (l * m) (u : BlockN L) = s151uSmul L l (s151uSmul L m (u : BlockN L))
      rw [s151uSmul_mk, s151uSmul_mk, s151uSmul_mk]
      congr 1
      apply Subtype.ext
      simp [mul_assoc]

theorem s151u_smul_mk (L : Subgroup G) (l : ↥L) (u : ↥(blockU L)) :
    l • (u : BlockN L) =
      ((⟨(l : G) * u * (l : G)⁻¹, s151u_conj_mem_U l u⟩ : ↥(blockU L)) : BlockN L) := rfl

theorem s151u_mk_eq_iff {L : Subgroup G} (u u' : ↥(blockU L)) :
    (u : BlockN L) = (u' : BlockN L) ↔ (u : G)⁻¹ * (u' : G) ∈ blockZ L := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  rfl

theorem s151u_fix_le_two [Finite G] {L B : Subgroup G} (hsh : IsShort2 L) (hB : IsSylowTwoOf B L)
    (hN : L ⊓ Subgroup.normalizer (B : Set G) ≤ B)
    (hmax3 : ∀ H : Subgroup G, IsMaxSubgroupIn L H → B ≤ H → Nat.card H = 3 * Nat.card B)
    (hcard : Nat.card ↥L = 3 * Nat.card B * (Nat.card (BlockN L) - 1))
    (hbig : 4 ≤ Nat.card (BlockN L)) :
    ∀ u ∈ blockU L, ∀ u' ∈ blockU L, u ∉ blockZ L → u' ∉ blockZ L →
      (∀ s ∈ B, s * u * s⁻¹ * u⁻¹ ∈ blockZ L) → (∀ s ∈ B, s * u' * s⁻¹ * u'⁻¹ ∈ blockZ L) →
      u⁻¹ * u' ∈ blockZ L := by
  classical
  intro u hu u' hu' huZ hu'Z hBu hBu'
  have hBL : B ≤ L := hB.1
  set BX : Subgroup ↥L := B.subgroupOf L with hBX
  have hBXcard : Nat.card BX = Nat.card B := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv
  have hmemBX : ∀ b : ↥L, b ∈ BX ↔ (b : G) ∈ B := fun b => Subgroup.mem_subgroupOf
  have hfixed : ∀ (v : G) (hv : v ∈ blockU L), (∀ s ∈ B, s * v * s⁻¹ * v⁻¹ ∈ blockZ L) →
      ∀ b ∈ BX, b • ((⟨v, hv⟩ : ↥(blockU L)) : BlockN L) = ((⟨v, hv⟩ : ↥(blockU L)) : BlockN L) := by
    intro v hv hBv b hb
    rw [s151u_smul_mk, s151u_mk_eq_iff]
    have hz := hBv (b : G) ((hmemBX b).mp hb)
    have hvL : v ∈ L := s151v_blockU_le_L hsh hv
    have hc := s151v_blockZ_comm hz (L.inv_mem hvL)
    show ((b : G) * v * (b : G)⁻¹)⁻¹ * v ∈ blockZ L
    have hw : v⁻¹ * ((b : G) * v * (b : G)⁻¹) ∈ blockZ L := by
      have e : v⁻¹ * ((b : G) * v * (b : G)⁻¹) = v⁻¹ * ((b : G) * v * (b : G)⁻¹ * v⁻¹) * v := by
        group
      rw [e]
      rw [inv_inv] at hc
      rw [hc]
      exact hz
    have := (blockZ L).inv_mem hw
    have e2 : (v⁻¹ * ((b : G) * v * (b : G)⁻¹))⁻¹ = ((b : G) * v * (b : G)⁻¹)⁻¹ * v := by group
    rwa [e2] at this
  have hne1 : ∀ (v : G) (hv : v ∈ blockU L), v ∉ blockZ L →
      ((⟨v, hv⟩ : ↥(blockU L)) : BlockN L) ≠ ((1 : ↥(blockU L)) : BlockN L) := by
    intro v hv hvZ h
    rw [s151u_mk_eq_iff] at h
    apply hvZ
    have : (v : G)⁻¹ ∈ blockZ L := by simpa using h
    simpa using (blockZ L).inv_mem this
  have ho : ∀ g : ↥L, g • ((1 : ↥(blockU L)) : BlockN L) = ((1 : ↥(blockU L)) : BlockN L) := by
    intro g
    rw [s151u_smul_mk]
    congr 1
    apply Subtype.ext
    simp
  have hB2 : IsPGroup 2 BX := hB.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hBL).symm
  have hno : ∀ ω : BlockN L, ω ≠ ((1 : ↥(blockU L)) : BlockN L) → ∃ g : ↥L, g • ω ≠ ω := by
    intro ω hω
    induction ω using QuotientGroup.induction_on with
    | H u₁ =>
      by_contra hcon
      push Not at hcon
      have hu₁Z : (u₁ : G) ∉ blockZ L := by
        intro hz
        apply hω
        rw [s151u_mk_eq_iff]
        simpa using (blockZ L).inv_mem hz
      have hu₁L : (u₁ : G) ∈ L := s151v_blockU_le_L hsh u₁.2
      have hfix : ∀ l ∈ L, l * (u₁ : G) * l⁻¹ * (u₁ : G)⁻¹ ∈ blockZ L := by
        intro l hl
        have h1 := hcon ⟨l, hl⟩
        rw [s151u_smul_mk, s151u_mk_eq_iff] at h1
        have hz : (l * (u₁ : G) * l⁻¹)⁻¹ * (u₁ : G) ∈ blockZ L := h1
        have hc := s151v_blockZ_comm ((blockZ L).inv_mem hz) hu₁L
        have e : l * (u₁ : G) * l⁻¹ * (u₁ : G)⁻¹ =
            (u₁ : G) * ((l * (u₁ : G) * l⁻¹)⁻¹ * (u₁ : G))⁻¹ * (u₁ : G)⁻¹ := by group
        rw [e, hc]
        exact (blockZ L).inv_mem hz
      obtain ⟨ω₂, hω₂o, hω₂ω⟩ : ∃ ω₂ : BlockN L, ω₂ ≠ ((1 : ↥(blockU L)) : BlockN L) ∧
          ω₂ ≠ (u₁ : BlockN L) := by
        by_contra hcon2
        push Not at hcon2
        have hle : Nat.card (BlockN L) ≤ Nat.card Bool := by
          refine Nat.card_le_card_of_injective
            (fun x => decide (x = ((1 : ↥(blockU L)) : BlockN L))) (fun x y hxy => ?_)
          by_cases hx : x = ((1 : ↥(blockU L)) : BlockN L) <;>
            by_cases hy : y = ((1 : ↥(blockU L)) : BlockN L)
          · rw [hx, hy]
          · simp [hx, hy] at hxy
          · simp [hx, hy] at hxy
          · rw [hcon2 x hx, hcon2 y hy]
        rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at hle
        omega
      induction ω₂ using QuotientGroup.induction_on with
      | H u₂ =>
        rcases s151u_fixed_by_L hsh u₁.2 hu₁Z hfix u₂ u₂.2 with h | h
        · apply hω₂o
          rw [s151u_mk_eq_iff]
          simpa using (blockZ L).inv_mem h
        · apply hω₂ω
          rw [s151u_mk_eq_iff]
          simpa using (blockZ L).inv_mem h
  have hsel : ∀ g ∈ Subgroup.normalizer (BX : Set ↥L), g ∈ BX := by
    intro g hg
    have hgn : (g : G) ∈ Subgroup.normalizer (B : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have hxL : x ∈ L := hBL hx
        have := (Subgroup.mem_normalizer_iff.mp hg ⟨x, hxL⟩).mp ((hmemBX _).mpr hx)
        exact (hmemBX _).mp this
      · intro hx
        have hgL : (g : G) * x * (g : G)⁻¹ ∈ L := hBL hx
        have hxL : x ∈ L := by
          have := L.mul_mem (L.mul_mem (L.inv_mem g.2) hgL) g.2
          simpa [mul_assoc] using this
        have := (Subgroup.mem_normalizer_iff.mp hg ⟨x, hxL⟩).mpr ((hmemBX _).mpr hx)
        exact (hmemBX _).mp this
    exact (hmemBX g).mpr (hN ⟨g.2, hgn⟩)
  have hmax : ∀ K : Subgroup ↥L, BX ≤ K → K ≠ ⊤ →
      ∃ H : Subgroup ↥L, K ≤ H ∧ H ≠ ⊤ ∧ Nat.card H = 3 * Nat.card BX := by
    intro K hBK hK
    have hKlt : K.map L.subtype < L := by
      refine lt_of_le_of_ne (Subgroup.map_subtype_le K) (fun h => hK ?_)
      have h2 : (K.map L.subtype).subgroupOf L = K :=
        Subgroup.comap_map_eq_self_of_injective L.subtype_injective K
      rw [← h2, h]
      simp
    obtain ⟨H₀, hH₀max, hKH₀⟩ := exists_isMaxSubgroupIn hKlt
    have hBK' : B ≤ K.map L.subtype := by
      intro b hb
      exact ⟨⟨b, hBL hb⟩, hBK ((hmemBX _).mpr hb), rfl⟩
    have hBH₀ : B ≤ H₀ := hBK'.trans hKH₀
    have hH₀L : H₀ ≤ L := hH₀max.1.le
    refine ⟨H₀.subgroupOf L, fun x hx => ?_, ?_, ?_⟩
    · exact hKH₀ ⟨x, hx, rfl⟩
    · intro h
      have : L ≤ H₀ := by
        intro x hx
        have : (⟨x, hx⟩ : ↥L) ∈ H₀.subgroupOf L := by rw [h]; trivial
        exact this
      exact hH₀max.1.ne (le_antisymm hH₀L this)
    · rw [hBXcard, ← hmax3 H₀ hH₀max hBH₀]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH₀L).toEquiv
  have hnum : Nat.card ↥L = 3 * Nat.card BX * (Nat.card (BlockN L) - 1) := by
    rw [hBXcard]
    exact hcard
  have key := s151u_orbit_fixed_le_one (X := ↥L) (Ω := BlockN L) ((1 : ↥(blockU L)) : BlockN L)
    ho BX hB2 hno hsel hmax hnum ((⟨u, hu⟩ : ↥(blockU L)) : BlockN L)
    ((⟨u', hu'⟩ : ↥(blockU L)) : BlockN L) (hne1 u hu huZ) (hne1 u' hu' hu'Z)
    (hfixed u hu hBu) (hfixed u' hu' hBu')
  exact (s151u_mk_eq_iff _ _).mp key.symm

end CFSG.Quasithin
