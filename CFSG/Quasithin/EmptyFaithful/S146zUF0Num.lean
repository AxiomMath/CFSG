module

public import CFSG.Quasithin.Background.FixVLattice
public import CFSG.Quasithin.Background.FixVZPowersMem
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.Quasithin.S146zU

@[expose] def cF {Y : Type*} [CommGroup Y] (A : Subgroup (MulAut Y)) (E : Subgroup Y) :
    Subgroup Y where
  carrier := {y | ∀ a ∈ A, a y * y⁻¹ ∈ E}
  one_mem' := fun a _ => by simp
  mul_mem' := fun {y z} hy hz a ha => by
    rw [map_mul, mul_inv, mul_mul_mul_comm]
    exact E.mul_mem (hy a ha) (hz a ha)
  inv_mem' := fun {y} hy a ha => by
    have h := E.inv_mem (hy a ha)
    rw [mul_inv, inv_inv] at h
    rwa [map_inv, inv_inv]

namespace UF0

variable {Y : Type*} [CommGroup Y]

theorem mem_cF {A : Subgroup (MulAut Y)} {E : Subgroup Y} {y : Y} :
    y ∈ cF A E ↔ ∀ a ∈ A, a y * y⁻¹ ∈ E := Iff.rfl

theorem fixV_sup_le_cF {A : Subgroup (MulAut Y)} {E : Subgroup Y}
    (hEA : ∀ a ∈ A, ∀ e ∈ E, a e ∈ E) : fixV A ⊔ E ≤ cF A E := by
  refine sup_le ?_ ?_
  · intro y hy a ha
    rw [hy a ha, mul_inv_cancel]
    exact E.one_mem
  · intro y hy a ha
    exact E.mul_mem (hEA a ha y hy) (E.inv_mem hy)

theorem mem_fixV_iff_le_stabilizer {B : Subgroup (MulAut Y)} {y : Y} :
    y ∈ fixV B ↔ B ≤ MulAction.stabilizer (MulAut Y) y :=
  ⟨fun h _ hx => MulAction.mem_stabilizer_iff.mpr (h _ hx),
    fun h _ hx => MulAction.mem_stabilizer_iff.mp (h hx)⟩

theorem fixV_sup (B₁ B₂ : Subgroup (MulAut Y)) : fixV (B₁ ⊔ B₂) = fixV B₁ ⊓ fixV B₂ :=
  CFSG.Quasithin.FixVLat.fixV_sup_eq B₁ B₂

theorem fixV_bot : fixV (⊥ : Subgroup (MulAut Y)) = ⊤ := by
  ext y
  rw [mem_fixV_iff_le_stabilizer]
  simp

theorem mem_fixV_zpowers {b : MulAut Y} {y : Y} :
    y ∈ fixV (Subgroup.zpowers b) ↔ b y = y :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem card_sup_mul_card_inf [Finite Y] (H K : Subgroup Y) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K := by
  have h1 : K.relIndex (K ⊔ H) * Nat.card ↥(K ⊓ (K ⊔ H)) = Nat.card ↥(K ⊔ H) :=
    Subgroup.relIndex_mul_card K (K ⊔ H)
  have h2 : K.relIndex H * Nat.card ↥(K ⊓ H) = Nat.card H := Subgroup.relIndex_mul_card K H
  rw [inf_sup_self, Subgroup.relIndex_sup_left] at h1
  rw [sup_comm, inf_comm, ← h1, ← h2]
  ring

theorem two_mul_card_le_of_lt {G : Type*} [Group G] [Finite G] {H K : Subgroup G} (h : H < K) :
    2 * Nat.card H ≤ Nat.card K := by
  have h1 : H.relIndex K * Nat.card ↥(H ⊓ K) = Nat.card K := Subgroup.relIndex_mul_card H K
  rw [inf_eq_left.mpr h.le] at h1
  have h2 : H.relIndex K ≠ 1 := fun h3 => h.not_ge (Subgroup.relIndex_eq_one.mp h3)
  have h3 : H.relIndex K ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact (Nat.card_pos (α := K)).ne h1
  have h4 : 2 ≤ H.relIndex K := by omega
  calc 2 * Nat.card H ≤ H.relIndex K * Nat.card H := Nat.mul_le_mul_right _ h4
    _ = Nat.card K := h1

theorem card_le_two_mul_card_inf [Finite Y] (K : Subgroup Y) (b : MulAut Y) (c : Y)
    (h : ∀ k ∈ K, b k * k⁻¹ = 1 ∨ b k * k⁻¹ = c) :
    Nat.card K ≤ 2 * Nat.card ↥(K ⊓ fixV (Subgroup.zpowers b)) := by
  let δ : Y →* Y := MonoidHom.mk' (fun y => b y * y⁻¹) fun x z => by
    rw [map_mul, mul_inv, mul_mul_mul_comm]
  have hker : δ.ker ⊓ K = K ⊓ fixV (Subgroup.zpowers b) := by
    ext y
    rw [Subgroup.mem_inf, Subgroup.mem_inf, mem_fixV_zpowers, MonoidHom.mem_ker, and_comm]
    refine and_congr_right fun _ => ?_
    simp [δ, mul_inv_eq_one]
  have h1 : δ.ker.relIndex K * Nat.card ↥(δ.ker ⊓ K) = Nat.card K :=
    Subgroup.relIndex_mul_card δ.ker K
  have h2 : δ.ker.relIndex K = Nat.card ↥(K.map δ) := Subgroup.relIndex_ker K δ
  have hsub : ((K.map δ : Subgroup Y) : Set Y) ⊆ {1, c} := by
    rintro _ ⟨k, hk, rfl⟩
    exact h k hk
  have h3 : Nat.card ↥(K.map δ) ≤ 2 :=
    calc Nat.card ↥(K.map δ) = Set.ncard ((K.map δ : Subgroup Y) : Set Y) :=
          (Nat.card_coe_set_eq _).symm
      _ ≤ Set.ncard ({1, c} : Set Y) := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := by simpa [Set.ncard_singleton] using Set.ncard_insert_le (1 : Y) {c}
  rw [hker, h2] at h1
  calc Nat.card K = Nat.card ↥(K.map δ) * Nat.card ↥(K ⊓ fixV (Subgroup.zpowers b)) := h1.symm
    _ ≤ 2 * Nat.card ↥(K ⊓ fixV (Subgroup.zpowers b)) := Nat.mul_le_mul_right _ h3

theorem card_le_mul_card_inf_fixV [Finite Y] (D : Subgroup Y) (c : Y) :
    ∀ (n : ℕ) (B : Subgroup (MulAut Y)), Nat.card B = n →
      (∀ b ∈ B, ∀ d ∈ D, b d * d⁻¹ = 1 ∨ b d * d⁻¹ = c) →
      Nat.card D ≤ Nat.card B * Nat.card ↥(D ⊓ fixV B) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro B hn hB
    by_cases hbot : B = ⊥
    · subst hbot
      simp [fixV_bot]
    · have hne : {C : Subgroup (MulAut Y) | C < B}.Nonempty :=
        ⟨⊥, bot_lt_iff_ne_bot.mpr hbot⟩
      obtain ⟨B', hB'mem, hB'max⟩ :=
        (Set.toFinite {C : Subgroup (MulAut Y) | C < B}).exists_maximal hne
      have hlt : B' < B := hB'mem
      obtain ⟨b, hbB, hbB'⟩ := IsConcreteLE.exists_of_lt hlt
      have hsup : B' ⊔ Subgroup.zpowers b = B := by
        by_contra hne2
        have hle : B' ⊔ Subgroup.zpowers b ≤ B :=
          sup_le hlt.le (Subgroup.zpowers_le.mpr hbB)
        have hlt2 : B' ⊔ Subgroup.zpowers b < B := lt_of_le_of_ne hle hne2
        exact hbB' (hB'max hlt2 le_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers b)))
      have h2 := two_mul_card_le_of_lt hlt
      have hpos : 0 < Nat.card B' := Nat.card_pos
      have hcardlt : Nat.card B' < n := by omega
      have ih' := ih (Nat.card B') hcardlt B' rfl (fun x hx => hB x (hlt.le hx))
      have hstep := card_le_two_mul_card_inf (D ⊓ fixV B') b c
        (fun k hk => hB b hbB k hk.1)
      have hKeq : D ⊓ fixV B' ⊓ fixV (Subgroup.zpowers b) = D ⊓ fixV B := by
        rw [inf_assoc, ← fixV_sup, hsup]
      rw [hKeq] at hstep
      calc Nat.card D ≤ Nat.card B' * Nat.card ↥(D ⊓ fixV B') := ih'
        _ ≤ Nat.card B' * (2 * Nat.card ↥(D ⊓ fixV B)) := Nat.mul_le_mul_left _ hstep
        _ = (2 * Nat.card B') * Nat.card ↥(D ⊓ fixV B) := by ring
        _ ≤ Nat.card B * Nat.card ↥(D ⊓ fixV B) := Nat.mul_le_mul_right _ (hn ▸ h2)

theorem arith_eq {r e ce f y cy : ℕ} (hr : 0 < r) (he : 0 < e) (hce : 0 < ce) (hf : 0 < f)
    (H1 : y ≤ r * r * cy) (H2 : r * ce ≤ e) (H3 : r * f ≤ y) (Ha : cy * e ≤ f * ce) :
    e = r * ce ∧ y = r * f ∧ y = r * r * cy := by
  have h1 : (r * ce) * (r * f) ≤ e * y := Nat.mul_le_mul H2 H3
  have h2 : e * y ≤ e * (r * r * cy) := Nat.mul_le_mul_left _ H1
  have h3 : e * (r * r * cy) ≤ (r * ce) * (r * f) :=
    calc e * (r * r * cy) = r * r * (cy * e) := by ring
      _ ≤ r * r * (f * ce) := Nat.mul_le_mul_left _ Ha
      _ = (r * ce) * (r * f) := by ring
  have hA : (r * ce) * (r * f) = e * y := le_antisymm h1 (h2.trans h3)
  have hB : e * y = e * (r * r * cy) := le_antisymm h2 (h3.trans h1)
  refine ⟨?_, ?_, Nat.eq_of_mul_eq_mul_left he hB⟩
  · by_contra hne
    have hlt : r * ce < e := lt_of_le_of_ne H2 (Ne.symm hne)
    have h4 : (r * ce) * (r * f) < e * (r * f) :=
      Nat.mul_lt_mul_of_pos_right hlt (Nat.mul_pos hr hf)
    have h5 : e * (r * f) ≤ e * y := Nat.mul_le_mul_left _ H3
    exact absurd hA (ne_of_lt (lt_of_lt_of_le h4 h5))
  · by_contra hne
    have hlt : r * f < y := lt_of_le_of_ne H3 (Ne.symm hne)
    have h4 : (r * ce) * (r * f) < (r * ce) * y :=
      Nat.mul_lt_mul_of_pos_left hlt (Nat.mul_pos hr hce)
    have h5 : (r * ce) * y ≤ e * y := Nat.mul_le_mul_right _ H2
    exact absurd hA (ne_of_lt (lt_of_lt_of_le h4 h5))

theorem counting_eq [Finite Y] {A : Subgroup (MulAut Y)} {E : Subgroup Y}
    (hEA : ∀ a ∈ A, ∀ e ∈ E, a e ∈ E)
    (H1 : Nat.card Y ≤ Nat.card A * Nat.card A * Nat.card ↥(fixV A))
    (H2 : Nat.card A * Nat.card ↥(E ⊓ fixV A) ≤ Nat.card E)
    (H3 : Nat.card A * Nat.card ↥(cF A E) ≤ Nat.card Y) :
    Nat.card E = Nat.card A * Nat.card ↥(E ⊓ fixV A) ∧
      Nat.card Y = Nat.card A * Nat.card ↥(cF A E) ∧
      Nat.card Y = Nat.card A * Nat.card A * Nat.card ↥(fixV A) := by
  have hprod := card_sup_mul_card_inf (fixV A) E
  rw [inf_comm] at hprod
  have hle := Subgroup.card_le_of_le (fixV_sup_le_cF hEA)
  have Ha : Nat.card ↥(fixV A) * Nat.card E ≤ Nat.card ↥(cF A E) * Nat.card ↥(E ⊓ fixV A) :=
    calc Nat.card ↥(fixV A) * Nat.card E
        = Nat.card ↥(fixV A ⊔ E) * Nat.card ↥(E ⊓ fixV A) := hprod.symm
      _ ≤ Nat.card ↥(cF A E) * Nat.card ↥(E ⊓ fixV A) := Nat.mul_le_mul_right _ hle
  exact arith_eq Nat.card_pos Nat.card_pos Nat.card_pos Nat.card_pos H1 H2 H3 Ha

theorem fixV_le_of_card [Finite Y] {A : Subgroup (MulAut Y)} {D : Subgroup Y} {c : Y}
    (H4a : Nat.card Y = Nat.card A * Nat.card D)
    (H4b : ∀ a ∈ A, ∀ d ∈ D, a d * d⁻¹ = 1 ∨ a d * d⁻¹ = c)
    (h : Nat.card Y = Nat.card A * Nat.card A * Nat.card ↥(fixV A)) : fixV A ≤ D := by
  have hD := card_le_mul_card_inf_fixV D c _ A rfl H4b
  have hr : 0 < Nat.card A := Nat.card_pos
  have h1 : Nat.card A * Nat.card A * Nat.card ↥(fixV A) ≤
      Nat.card A * Nat.card A * Nat.card ↥(D ⊓ fixV A) :=
    calc Nat.card A * Nat.card A * Nat.card ↥(fixV A) = Nat.card A * Nat.card D := by
          rw [← h, H4a]
      _ ≤ Nat.card A * (Nat.card A * Nat.card ↥(D ⊓ fixV A)) := Nat.mul_le_mul_left _ hD
      _ = Nat.card A * Nat.card A * Nat.card ↥(D ⊓ fixV A) := by ring
  have h2 : Nat.card ↥(fixV A) ≤ Nat.card ↥(D ⊓ fixV A) :=
    Nat.le_of_mul_le_mul_left h1 (Nat.mul_pos hr hr)
  exact inf_eq_right.mp (Subgroup.eq_of_le_of_card_ge inf_le_right h2)

theorem inf_le_fixV [Finite Y] {A : Subgroup (MulAut Y)} {E D : Subgroup Y} {c : Y}
    (H4b : ∀ a ∈ A, ∀ d ∈ D, a d * d⁻¹ = 1 ∨ a d * d⁻¹ = c)
    (H5 : ∀ s ∈ E, s ∉ fixV A → 4 ≤ (Set.range fun a : ↥A => (a : MulAut Y) s).ncard) :
    E ⊓ D ≤ fixV A := by
  intro s hs
  by_contra hsfix
  have h4 := H5 s hs.1 hsfix
  have hsub : (Set.range fun a : ↥A => (a : MulAut Y) s) ⊆ {s, c * s} := by
    rintro _ ⟨a, rfl⟩
    rcases H4b a a.2 s hs.2 with h | h
    · exact Or.inl (mul_inv_eq_one.mp h)
    · exact Or.inr (mul_inv_eq_iff_eq_mul.mp h)
  have h2 : (Set.range fun a : ↥A => (a : MulAut Y) s).ncard ≤ 2 :=
    (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
      (by simpa [Set.ncard_singleton] using Set.ncard_insert_le s {c * s})
  omega

theorem sup_eq_top [Finite Y] {A : Subgroup (MulAut Y)} {E D : Subgroup Y}
    (hE : Nat.card E = Nat.card A * Nat.card ↥(E ⊓ fixV A))
    (hY : Nat.card Y = Nat.card A * Nat.card D)
    (hle : fixV A ≤ D) (hle2 : E ⊓ D ≤ fixV A) : E ⊔ D = ⊤ := by
  have hEq : E ⊓ D = E ⊓ fixV A := le_antisymm (le_inf inf_le_left hle2) (inf_le_inf_left E hle)
  have hprod := card_sup_mul_card_inf E D
  rw [hEq] at hprod
  apply Subgroup.eq_top_of_card_eq
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥(E ⊓ fixV A)))
  calc Nat.card ↥(E ⊔ D) * Nat.card ↥(E ⊓ fixV A) = Nat.card E * Nat.card D := hprod
    _ = Nat.card Y * Nat.card ↥(E ⊓ fixV A) := by rw [hY, hE]; ring

theorem four_le_ncard_of_stabilizer [Finite Y] (A : Subgroup (MulAut Y)) (s : Y)
    (h : 4 * Nat.card ↥(MulAction.stabilizer ↥A s) ≤ Nat.card ↥A) :
    4 ≤ (Set.range fun a : ↥A => (a : MulAut Y) s).ncard := by
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer (↥A) s)
  have h2 : (Set.range fun a : ↥A => (a : MulAut Y) s) = MulAction.orbit (↥A) s := rfl
  have h3 : 0 < Nat.card ↥(MulAction.stabilizer (↥A) s) := Nat.card_pos
  rw [h2, ← MulAction.index_stabilizer]
  by_contra hlt
  have h4 := Nat.mul_lt_mul_of_pos_left (not_le.mp hlt) h3
  omega

theorem comm_mem_or {A : Subgroup (MulAut Y)} {E D : Subgroup Y} {c : Y}
    (hEA : ∀ a ∈ A, ∀ e ∈ E, a e ∈ E)
    (H4b : ∀ a ∈ A, ∀ d ∈ D, a d * d⁻¹ = 1 ∨ a d * d⁻¹ = c) (htop : E ⊔ D = ⊤)
    {a : MulAut Y} (ha : a ∈ A) (y : Y) : a y * y⁻¹ ∈ E ∨ c⁻¹ * (a y * y⁻¹) ∈ E := by
  have hy : y ∈ E ⊔ D := htop ▸ Subgroup.mem_top y
  obtain ⟨e, he, d, hd, rfl⟩ := Subgroup.mem_sup.mp hy
  have hmul : a (e * d) * (e * d)⁻¹ = (a e * e⁻¹) * (a d * d⁻¹) := by
    rw [map_mul, mul_inv, mul_mul_mul_comm]
  have hE : a e * e⁻¹ ∈ E := E.mul_mem (hEA a ha e he) (E.inv_mem he)
  rw [hmul]
  rcases H4b a ha d hd with h | h
  · rw [h, mul_one]
    exact Or.inl hE
  · rw [h]
    refine Or.inr ?_
    rwa [mul_comm (a e * e⁻¹) c, ← mul_assoc, inv_mul_cancel, one_mul]

end UF0

theorem numerics_core {Y : Type*} [CommGroup Y] [Finite Y] {A : Subgroup (MulAut Y)}
    {E : Subgroup Y} (hEA : ∀ a ∈ A, ∀ e ∈ E, a e ∈ E)
    (H1 : Nat.card Y ≤ Nat.card A * Nat.card A * Nat.card ↥(fixV A))
    (H2 : Nat.card A * Nat.card ↥(E ⊓ fixV A) ≤ Nat.card E)
    (H3 : Nat.card A * Nat.card ↥(cF A E) ≤ Nat.card Y)
    {D : Subgroup Y} (H4a : Nat.card Y = Nat.card A * Nat.card D)
    {c : Y} (H4b : ∀ a ∈ A, ∀ d ∈ D, a d * d⁻¹ = 1 ∨ a d * d⁻¹ = c)
    (H5 : Nat.card E = Nat.card A * Nat.card ↥(E ⊓ fixV A) →
      ∀ s ∈ E, s ∉ fixV A → 4 ≤ (Set.range fun a : ↥A => (a : MulAut Y) s).ncard)
    (H5F : Nat.card Y = Nat.card A * Nat.card ↥(cF A E) →
      ∃ y₁ y₂ : Y, ∃ a₁ ∈ A, ∃ a₂ ∈ A, a₁ y₁ * y₁⁻¹ ∉ E ∧ a₂ y₂ * y₂⁻¹ ∉ E ∧
        (a₁ y₁ * y₁⁻¹)⁻¹ * (a₂ y₂ * y₂⁻¹) ∉ E) :
    False := by
  obtain ⟨hE, hF, hY⟩ := UF0.counting_eq hEA H1 H2 H3
  have hfix : fixV A ≤ D := UF0.fixV_le_of_card H4a H4b hY
  have hinf : E ⊓ D ≤ fixV A := UF0.inf_le_fixV H4b (H5 hE)
  have htop : E ⊔ D = ⊤ := UF0.sup_eq_top hE H4a hfix hinf
  obtain ⟨y₁, y₂, a₁, ha₁, a₂, ha₂, h1, h2, h3⟩ := H5F hF
  have k1 : c⁻¹ * (a₁ y₁ * y₁⁻¹) ∈ E :=
    (UF0.comm_mem_or hEA H4b htop ha₁ y₁).resolve_left h1
  have k2 : c⁻¹ * (a₂ y₂ * y₂⁻¹) ∈ E :=
    (UF0.comm_mem_or hEA H4b htop ha₂ y₂).resolve_left h2
  apply h3
  have key : ∀ u v : Y, u⁻¹ * v = (c⁻¹ * u)⁻¹ * (c⁻¹ * v) := fun u v => by
    rw [mul_inv, inv_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]
  rw [key]
  exact E.mul_mem (E.inv_mem k1) k2

end CFSG.Quasithin.S146zU
