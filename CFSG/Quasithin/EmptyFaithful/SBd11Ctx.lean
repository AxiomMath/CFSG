module

public import CFSG.Quasithin.EmptyFaithful.S153D35
public import CFSG.Quasithin.EmptyFaithful.SBd11Syl

public section

namespace CFSG.Quasithin.SBd11

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem false_of_pCoreOf_three_ne_bot (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) (hYL : Yp ≤ L)
    (h3 : pCoreOf 3 Yp ≠ ⊥) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLI : L ≤ I := le_of_mem_cComp c.c33.mem
  have hYI : Yp ≤ I := hYL.trans hLI
  have hnorm := c.facts.norm_eq
  have hMIN : M ⊓ I ≤ Subgroup.normalizer (Yp : Set G) := fun g hg => by
    have : g ∈ I ⊓ Subgroup.normalizer (Yp : Set G) := by rw [hnorm]; exact hg
    exact this.2
  have hYMI : Yp ≤ M ⊓ I := fun y hy => by
    have : y ∈ I ⊓ Subgroup.normalizer (Yp : Set G) := ⟨hYI hy, Subgroup.le_normalizer hy⟩
    rw [hnorm] at this
    exact this
  have hXMI : pCoreOf 3 Yp ≤ M ⊓ I := (pCoreOf_le 3 Yp).trans hYMI
  have hMIX : M ⊓ I ≤ Subgroup.normalizer (pCoreOf 3 Yp : Set G) :=
    hMIN.trans (normalizer_le_normalizer_pCoreOf 3 Yp)
  have hRMI : pCoreOf 2 (M ⊓ I) ≤ M ⊓ I := pCoreOf_le 2 _
  have hMIR : M ⊓ I ≤ Subgroup.normalizer (pCoreOf 2 (M ⊓ I) : Set G) :=
    le_normalizer_pCoreOf 2 _
  have hXp : IsPGroup 3 (pCoreOf 3 Yp) := pCoreOf_isPGroup 3 Yp
  have hRp : IsPGroup 2 (pCoreOf 2 (M ⊓ I)) := pCoreOf_isPGroup 2 _
  have hdis : pCoreOf 3 Yp ⊓ pCoreOf 2 (M ⊓ I) = ⊥ := by
    refine disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard ?_)
    exact IsPGroup.coprime_card_of_ne 3 2 (by norm_num) _ _ hXp hRp
  have hXC : pCoreOf 3 Yp ≤ Subgroup.centralizer (pCoreOf 2 (M ⊓ I) : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have h1 : x * r * x⁻¹ * r⁻¹ ∈ pCoreOf 2 (M ⊓ I) :=
      (pCoreOf 2 (M ⊓ I)).mul_mem
        ((Subgroup.mem_normalizer_iff.1 (hMIR (hXMI hx)) r).1 hr)
        ((pCoreOf 2 (M ⊓ I)).inv_mem hr)
    have h2 : x * r * x⁻¹ * r⁻¹ ∈ pCoreOf 3 Yp := by
      have : x * (r * x⁻¹ * r⁻¹) ∈ pCoreOf 3 Yp :=
        (pCoreOf 3 Yp).mul_mem hx
          ((Subgroup.mem_normalizer_iff.1 (hMIX (hRMI hr)) x⁻¹).1 ((pCoreOf 3 Yp).inv_mem hx))
      simpa [mul_assoc] using this
    have h3 : x * r * x⁻¹ * r⁻¹ ∈ pCoreOf 3 Yp ⊓ pCoreOf 2 (M ⊓ I) := ⟨h2, h1⟩
    rw [hdis, Subgroup.mem_bot] at h3
    calc r * x = (x * r * x⁻¹ * r⁻¹)⁻¹ * (x * r) := by group
      _ = x * r := by rw [h3]; group
  have hXR : pCoreOf 3 Yp ≤ pCoreOf 2 (M ⊓ I) := fun x hx =>
    c.charTwo_MI ⟨hXMI hx, hXC hx⟩
  apply h3
  rw [eq_bot_iff, ← hdis]
  exact le_inf le_rfl hXR


omit [Finite G] in
theorem mem_centerOf_iff_center {L : Subgroup G} {x : ↥L} :
    (x : G) ∈ centerOf L ↔ x ∈ Subgroup.center ↥L := by
  constructor
  · rintro ⟨-, hx⟩
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx g g.2)
  · intro hx
    refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨h, hh⟩)

theorem isPGroup_center_of_center_eq {L : Subgroup G} (h : centerOf L = pCoreOf 2 L) :
    IsPGroup 2 (Subgroup.center ↥L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro z
  have hz : ((z : ↥L) : G) ∈ pCoreOf 2 L := by
    rw [← h]
    exact mem_centerOf_iff_center.2 z.2
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L ⟨_, hz⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg (fun w : ↥(pCoreOf 2 L) => (w : G)) hk
  simpa using this

omit [Finite G] in
theorem card_form_of_struct [Finite G] {H : Subgroup G}
    (hq : IsElemAbelianOfRank 3 2 (OTwoQuot H) ∨ IsPOnePlusTwo 3 (OTwoQuot H)) :
    ∃ b k : ℕ, 2 ≤ k ∧ Nat.card (CFSG.Open.pCore 2 ↥H) = 2 ^ b ∧ Nat.card H = 2 ^ b * 3 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Nat.card ↥H = Nat.card (↥H ⧸ CFSG.Open.pCore 2 ↥H) * Nat.card (CFSG.Open.pCore 2 ↥H) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥H)
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card).1
    (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥H) 2)
  have hQ : ∃ k, 2 ≤ k ∧ Nat.card (OTwoQuot H) = 3 ^ k := by
    rcases hq with h | ⟨-, h3, -⟩
    · obtain ⟨e⟩ : Nonempty (OTwoQuot H ≃* Multiplicative (Fin 2 → ZMod 3)) := h
      refine ⟨2, le_rfl, ?_⟩
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
      simp [Fintype.card_multiplicative, ZMod.card]
    · exact ⟨3, by norm_num, h3⟩
  obtain ⟨k, hk, hQk⟩ := hQ
  refine ⟨b, k, hk, hb, ?_⟩
  rw [h1, hb]
  have : Nat.card (↥H ⧸ CFSG.Open.pCore 2 ↥H) = 3 ^ k := hQk
  rw [this, mul_comm]

omit [Finite G] in
theorem pCoreOf_three_ne_bot_of_normal {H : Subgroup G} (R : Subgroup ↥H) (hR : R ≠ ⊥)
    (hn : R.Normal) (hp : IsPGroup 3 R) : pCoreOf 3 H ≠ ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : R.map H.subtype ≤ pCoreOf 3 H := by
    refine le_pCoreOf 3 (Subgroup.map_subtype_le R) ?_ (hp.map H.subtype)
    rw [show (R.map H.subtype).subgroupOf H = R from
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective R]
    exact hn
  intro h
  apply hR
  rw [h, le_bot_iff] at hle
  exact Subgroup.map_injective H.subtype_injective (hle.trans (Subgroup.map_bot _).symm)

theorem false_of_alt7 (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) (hYL : Yp ≤ L)
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 7)) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨b, k, hk2, -, hcard⟩ := card_form_of_struct c.facts11.struct_Yp
  have hcen : IsPGroup 2 (Subgroup.center ↥L) := isPGroup_center_of_center_eq c.c33.center_eq
  let ψ : ↥Yp →* ↥L ⧸ Subgroup.center ↥L :=
    (QuotientGroup.mk' (Subgroup.center ↥L)).comp (Subgroup.inclusion hYL)
  have hker : ∀ z : ↥Yp, z ∈ ψ.ker ↔ Subgroup.inclusion hYL z ∈ Subgroup.center ↥L := fun z => by
    simp [ψ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have hZ2 : IsPGroup 2 ψ.ker := by
    intro z
    obtain ⟨m, hm⟩ := hcen ⟨_, (hker z.1).1 z.2⟩
    refine ⟨m, Subtype.ext ?_⟩
    have h1 := congrArg (fun w : ↥(Subgroup.center ↥L) => (w : ↥L)) hm
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h1
    apply Subgroup.inclusion_injective hYL
    simpa [map_pow] using h1
  have hcomm : ∀ z ∈ ψ.ker, ∀ x : ↥Yp, z * x = x * z := by
    intro z hz x
    have h1 := Subgroup.mem_center_iff.1 ((hker z).1 hz) (Subgroup.inclusion hYL x)
    apply Subgroup.inclusion_injective hYL
    simpa [map_mul] using h1.symm
  have hL7 : Nat.card (↥L ⧸ Subgroup.center ↥L) = 2520 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]
  have hr : Nat.card ψ.range ∣ 2520 := hL7 ▸ Subgroup.card_subgroup_dvd_card ψ.range
  have hprod := Subgroup.card_ker_mul_card_range ψ
  obtain ⟨P⟩ : Nonempty (Sylow 3 ↥Yp) := inferInstance
  have h9 : 9 ∣ Nat.card P := by
    refine pow_dvd_card_sylow (k := 2) P ?_
    rw [hcard]
    exact Dvd.dvd.mul_left (pow_dvd_pow 3 hk2) _
  have hr72 : Nat.card ψ.range ∣ 72 := by
    have h1 : Nat.card ψ.range ∣ 2 ^ b * 3 ^ k := by
      rw [← hcard, ← hprod]
      exact Dvd.intro_left _ rfl
    have hcop : Nat.Coprime (Nat.card ψ.range) 35 :=
      Nat.Coprime.coprime_dvd_left h1
        (Nat.coprime_mul_iff_left.2 ⟨Nat.Coprime.pow_left b (by norm_num),
          Nat.Coprime.pow_left k (by norm_num)⟩)
    exact hcop.dvd_of_dvd_mul_right (show Nat.card ψ.range ∣ 72 * 35 by simpa using hr)
  have hcard' : Nat.card ↥Yp ∣ 8 * Nat.card ψ.ker * Nat.card P := by
    rw [← hprod]
    have h72 : (72 : ℕ) ∣ 8 * Nat.card P := Nat.mul_dvd_mul_left 8 h9
    calc Nat.card ψ.ker * Nat.card ψ.range ∣ Nat.card ψ.ker * 72 :=
          Nat.mul_dvd_mul_left _ hr72
      _ ∣ Nat.card ψ.ker * (8 * Nat.card P) := Nat.mul_dvd_mul_left _ h72
      _ = 8 * Nat.card ψ.ker * Nat.card P := by ring
  obtain ⟨R, hR0, hRn, hRp⟩ :=
    exists_normal_three_of_card_dvd P h9 hZ2 (fun z hz x _ => hcomm z hz x) hcard'
  exact false_of_pCoreOf_three_ne_bot c hYL (pCoreOf_three_ne_bot_of_normal R hR0 hRn hRp)

end CFSG.Quasithin.SBd11
