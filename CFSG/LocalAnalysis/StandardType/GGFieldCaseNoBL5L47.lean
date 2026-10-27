module

public import CFSG.LocalAnalysis.StandardType.GGFieldCase

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

open scoped commutatorElement

section General

variable {G : Type*} [Group G]

@[expose] def ggPowSubgroup (U₁ : Subgroup G) (hU₁ : IsMulCommutative U₁) (n : ℕ) :
    Subgroup G where
  carrier := {w | ∃ u ∈ U₁, u ^ n = w}
  mul_mem' := by
    rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    refine ⟨u * v, U₁.mul_mem hu hv, ?_⟩
    have hc : Commute u v := congrArg Subtype.val (hU₁.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
    exact hc.mul_pow n
  one_mem' := ⟨1, U₁.one_mem, one_pow n⟩
  inv_mem' := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u⁻¹, U₁.inv_mem hu, inv_pow u n⟩

theorem mem_ggPowSubgroup {U₁ : Subgroup G} {hU₁ : IsMulCommutative U₁} {n : ℕ} {w : G} :
    w ∈ ggPowSubgroup U₁ hU₁ n ↔ ∃ u ∈ U₁, u ^ n = w :=
  Iff.rfl

@[expose] def ggFlagStab (B₁ W₀ : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (B₁ : Set G) ∧
    (∀ b ∈ B₁, b⁻¹ * (g⁻¹ * b * g) ∈ W₀) ∧ ∀ w ∈ W₀, g⁻¹ * w * g = w}
  mul_mem' := by
    rintro g h ⟨hgN, hgB, hgW⟩ ⟨hhN, hhB, hhW⟩
    refine ⟨Subgroup.mul_mem _ hgN hhN, fun b hb => ?_, fun w hw => ?_⟩
    · have hc := hgB b hb
      have hc' := hhB b hb
      have e : b⁻¹ * ((g * h)⁻¹ * b * (g * h)) =
          (b⁻¹ * (h⁻¹ * b * h)) * (h⁻¹ * (b⁻¹ * (g⁻¹ * b * g)) * h) := by group
      rw [e, hhW _ hc]
      exact W₀.mul_mem hc' hc
    · have e : (g * h)⁻¹ * w * (g * h) = h⁻¹ * (g⁻¹ * w * g) * h := by group
      rw [e, hgW w hw, hhW w hw]
  one_mem' := ⟨Subgroup.one_mem _, fun b _ => by simp, fun w _ => by simp⟩
  inv_mem' := by
    rintro g ⟨hgN, hgB, hgW⟩
    refine ⟨Subgroup.inv_mem _ hgN, fun b hb => ?_, fun w hw => ?_⟩
    · have hb' : g * b * g⁻¹ ∈ B₁ := (Subgroup.mem_normalizer_iff.mp hgN b).mp hb
      have hc := W₀.inv_mem (hgB _ hb')
      have e : (g * b * g⁻¹)⁻¹ * (g⁻¹ * (g * b * g⁻¹) * g) = (g * b * g⁻¹)⁻¹ * b := by group
      rw [e] at hc
      have e2 : b⁻¹ * (g⁻¹⁻¹ * b * g⁻¹) = ((g * b * g⁻¹)⁻¹ * b)⁻¹ := by group
      rw [e2]
      exact hc
    · have h1 := hgW w hw
      calc g⁻¹⁻¹ * w * g⁻¹ = g * (g⁻¹ * w * g) * g⁻¹ := by rw [h1, inv_inv]
        _ = w := by group

theorem conj_mem_ggFlagStab {B₁ W₀ : Subgroup G} {m g : G}
    (hmB : m ∈ Subgroup.normalizer (B₁ : Set G)) (hmW : m ∈ Subgroup.normalizer (W₀ : Set G))
    (hg : g ∈ ggFlagStab B₁ W₀) : m * g * m⁻¹ ∈ ggFlagStab B₁ W₀ := by
  obtain ⟨hgN, hgB, hgW⟩ := hg
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hmB hgN) (Subgroup.inv_mem _ hmB),
    fun b hb => ?_, fun w hw => ?_⟩
  · have hb₀ : m⁻¹ * b * m ∈ B₁ := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hmB) b).mp hb
      simpa using this
    have hc := hgB _ hb₀
    have hc' : m * ((m⁻¹ * b * m)⁻¹ * (g⁻¹ * (m⁻¹ * b * m) * g)) * m⁻¹ ∈ W₀ :=
      (Subgroup.mem_normalizer_iff.mp hmW _).mp hc
    have e : b⁻¹ * ((m * g * m⁻¹)⁻¹ * b * (m * g * m⁻¹)) =
        m * ((m⁻¹ * b * m)⁻¹ * (g⁻¹ * (m⁻¹ * b * m) * g)) * m⁻¹ := by group
    rw [e]
    exact hc'
  · have hw₀ : m⁻¹ * w * m ∈ W₀ := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hmW) w).mp hw
      simpa using this
    have e : (m * g * m⁻¹)⁻¹ * w * (m * g * m⁻¹) = m * (g⁻¹ * (m⁻¹ * w * m) * g) * m⁻¹ := by
      group
    rw [e, hgW _ hw₀]
    group

theorem pow_mem_centralizer_of_mem_ggFlagStab {p : ℕ} {B₁ W₀ : Subgroup G}
    (hW₀ : ∀ w ∈ W₀, w ^ p = 1) {g : G} (hg : g ∈ ggFlagStab B₁ W₀) :
    g ^ p ∈ Subgroup.centralizer (B₁ : Set G) := by
  obtain ⟨-, hgB, hgW⟩ := hg
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  set c := b⁻¹ * (g⁻¹ * b * g) with hc
  have hcW : c ∈ W₀ := hgB b hb
  have hbc : g⁻¹ * b * g = b * c := by rw [hc]; group
  have hiter : ∀ n : ℕ, (g ^ n)⁻¹ * b * g ^ n = b * c ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : (g ^ (n + 1))⁻¹ * b * g ^ (n + 1) = g⁻¹ * ((g ^ n)⁻¹ * b * g ^ n) * g := by
        rw [pow_succ]
        group
      have e3 : g⁻¹ * c ^ n * g = c ^ n := by
        have h := conj_pow (a := g⁻¹) (b := c) (i := n)
        rw [inv_inv] at h
        rw [← h, hgW c hcW]
      have e2 : g⁻¹ * (b * c ^ n) * g = (g⁻¹ * b * g) * (g⁻¹ * c ^ n * g) := by group
      rw [e, ih, e2, hbc, e3, pow_succ']
      group
  have h := hiter p
  rw [hW₀ c hcW, mul_one] at h
  calc b * g ^ p = g ^ p * ((g ^ p)⁻¹ * b * g ^ p) := by group
    _ = g ^ p * b := by rw [h]

theorem exists_mul_mem_normalizer_of_maxPSubgroup [Finite G] {p : ℕ} [Fact p.Prime]
    {C U : Subgroup G} {n : G} (hn : n ∈ Subgroup.normalizer (C : Set G)) (hUp : IsPGroup p U)
    (hUC : U ≤ C) (hmax : ∀ Q : Subgroup G, Q ≤ C → IsPGroup p Q → U ≤ Q → Q = U) :
    ∃ c ∈ C, c * n ∈ Subgroup.normalizer (U : Set G) := by
  obtain ⟨S, hS⟩ := (hUp.comap_subtype (K := C)).exists_le_sylow
  have hSU : (S : Subgroup C).map C.subtype = U :=
    hmax _ (Subgroup.map_subtype_le _) (S.isPGroup'.map _)
      (fun u hu => ⟨⟨u, hUC hu⟩, hS (Subgroup.mem_subgroupOf.mpr hu), rfl⟩)
  have hVC : ∀ u ∈ U, n * u * n⁻¹ ∈ C := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp hn u).mp (hUC hu)
  have hVp : IsPGroup p ((U.map (MulAut.conj n).toMonoidHom).subgroupOf C) :=
    (hUp.map _).comap_subtype
  obtain ⟨T, hT⟩ := hVp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (↥C) T S
  have key : ∀ u ∈ U, (c * n)⁻¹⁻¹ * u * (c * n)⁻¹ ∈ U := by
    intro u hu
    have h1 : (⟨n * u * n⁻¹, hVC u hu⟩ : C) ∈ (T : Subgroup C) :=
      hT (Subgroup.mem_subgroupOf.mpr ⟨u, hu, by simp [MulAut.conj_apply]⟩)
    have h2 : MulAut.conj c • (⟨n * u * n⁻¹, hVC u hu⟩ : C) ∈ (S : Subgroup C) := by
      rw [← hc, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ h1
    rw [← hSU]
    refine ⟨_, h2, ?_⟩
    simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_subtype, Subgroup.coe_mul,
      Subgroup.coe_inv, inv_inv, mul_inv_rev]
    group
  refine ⟨c, c.2, ?_⟩
  have := Subgroup.inv_mem _ (mem_normalizer_of_forall_conj_mem key)
  simpa using this

theorem conj_pow_eq_mul_pow {a u : G} (h : (u⁻¹ * (a⁻¹ * u * a)) * a = a * (u⁻¹ * (a⁻¹ * u * a)))
    (n : ℕ) : (a ^ n)⁻¹ * u * a ^ n = u * (u⁻¹ * (a⁻¹ * u * a)) ^ n := by
  set δ := u⁻¹ * (a⁻¹ * u * a) with hδ
  have hδa : a⁻¹ * δ * a = δ := by
    calc a⁻¹ * δ * a = a⁻¹ * (δ * a) := by group
      _ = a⁻¹ * (a * δ) := by rw [h]
      _ = δ := by group
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (a ^ (n + 1))⁻¹ * u * a ^ (n + 1) = a⁻¹ * ((a ^ n)⁻¹ * u * a ^ n) * a := by
      rw [pow_succ]
      group
    have e3 : a⁻¹ * δ ^ n * a = δ ^ n := by
      have h' := conj_pow (a := a⁻¹) (b := δ) (i := n)
      rw [inv_inv] at h'
      rw [← h', hδa]
    have e2 : a⁻¹ * (u * δ ^ n) * a = (a⁻¹ * u * a) * (a⁻¹ * δ ^ n * a) := by group
    have e4 : a⁻¹ * u * a = u * δ := by rw [hδ]; group
    rw [e, ih, e2, e3, e4, pow_succ']
    group

theorem card_ker_powMonoidHom_le {A : Type*} [CommGroup A] [Finite A] (p : ℕ) :
    ∀ k : ℕ, Nat.card (powMonoidHom (p ^ k) : A →* A).ker ≤
      Nat.card (powMonoidHom p : A →* A).ker ^ k
  | 0 => by
    have h : (powMonoidHom (p ^ 0) : A →* A).ker = ⊥ := by
      ext a
      simp [powMonoidHom]
    rw [h, Subgroup.card_bot, pow_zero]
  | k + 1 => by
    set K := (powMonoidHom (p ^ (k + 1)) : A →* A).ker with hK
    let ψ : K →* A := (powMonoidHom p).comp K.subtype
    have h1 : Nat.card K = Nat.card ψ.ker * Nat.card ψ.range := by
      rw [← Subgroup.index_ker, Subgroup.card_mul_index]
    have h2 : Nat.card ψ.ker ≤ Nat.card (powMonoidHom p : A →* A).ker := by
      rw [← Subgroup.card_map_of_injective K.subtype_injective]
      apply Subgroup.card_le_of_le
      rintro _ ⟨a, ha, rfl⟩
      exact ha
    have h3 : Nat.card ψ.range ≤ Nat.card (powMonoidHom (p ^ k) : A →* A).ker := by
      apply Subgroup.card_le_of_le
      rintro _ ⟨a, rfl⟩
      have ha : (a : A) ^ p ^ (k + 1) = 1 := a.2
      change ((a : A) ^ p) ^ p ^ k = 1
      rw [← pow_mul, ← pow_succ']
      exact ha
    calc Nat.card K = Nat.card ψ.ker * Nat.card ψ.range := h1
      _ ≤ Nat.card (powMonoidHom p : A →* A).ker *
          Nat.card (powMonoidHom (p ^ k) : A →* A).ker := Nat.mul_le_mul h2 h3
      _ ≤ Nat.card (powMonoidHom p : A →* A).ker *
          Nat.card (powMonoidHom p : A →* A).ker ^ k :=
        Nat.mul_le_mul_left _ (card_ker_powMonoidHom_le p k)
      _ = Nat.card (powMonoidHom p : A →* A).ker ^ (k + 1) := by ring

theorem card_le_mul_card_ggPowSubgroup [Finite G] {p s r : ℕ} (hp : p.Prime) (hs : 1 ≤ s)
    {U₁ B₁ H : Subgroup G} (hU₁ : IsMulCommutative U₁)
    (hB₁ : ∀ u : G, u ∈ B₁ ↔ u ∈ U₁ ∧ u ^ p = 1) (hHU₁ : H ≤ U₁)
    (hHcard : Nat.card H = p ^ (s * r)) (hHB₁ : Nat.card (H ⊓ B₁ : Subgroup G) = p ^ r)
    (hB₁card : Nat.card B₁ ≤ p ^ (r + 1)) :
    Nat.card B₁ ≤ p * Nat.card (ggPowSubgroup U₁ hU₁ (p ^ (s - 1))) := by
  have hHab : ∀ a b : H, a * b = b * a := fun a b => Subtype.ext
    (show (a : G) * b = b * a from
      congrArg Subtype.val (hU₁.is_comm.comm ⟨a, hHU₁ a.2⟩ ⟨b, hHU₁ b.2⟩))
  let _ : CommGroup H := { (inferInstance : Group H) with mul_comm := hHab }
  have hmap : (powMonoidHom p : H →* H).ker.map H.subtype = H ⊓ B₁ := by
    ext g
    simp only [Subgroup.mem_map, MonoidHom.mem_ker, powMonoidHom_apply, Subgroup.coe_subtype,
      Subgroup.mem_inf]
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ⟨h.2, (hB₁ h).mpr ⟨hHU₁ h.2, by simpa using congrArg Subtype.val hh⟩⟩
    · rintro ⟨hgH, hgB⟩
      exact ⟨⟨g, hgH⟩, Subtype.ext (by simpa using ((hB₁ g).mp hgB).2), rfl⟩
  have hΩ1 : Nat.card (powMonoidHom p : H →* H).ker = p ^ r := by
    rw [← hHB₁, ← hmap, Subgroup.card_map_of_injective H.subtype_injective]
  have hΩ := card_ker_powMonoidHom_le (A := H) p (s - 1)
  rw [hΩ1, ← pow_mul] at hΩ
  have hcard : Nat.card H = Nat.card (powMonoidHom (p ^ (s - 1)) : H →* H).ker *
      Nat.card (powMonoidHom (p ^ (s - 1)) : H →* H).range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have h2 : p ^ (s * r) = p ^ (r * (s - 1)) * p ^ r := by
    rw [← pow_add]
    congr 1
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    ring
  have hrange : p ^ r ≤ Nat.card (powMonoidHom (p ^ (s - 1)) : H →* H).range := by
    have h1 : p ^ (r * (s - 1)) * p ^ r ≤
        p ^ (r * (s - 1)) * Nat.card (powMonoidHom (p ^ (s - 1)) : H →* H).range := by
      rw [← h2, ← hHcard, hcard]
      exact Nat.mul_le_mul_right _ hΩ
    exact Nat.le_of_mul_le_mul_left h1 (pow_pos hp.pos _)
  have hle : Nat.card (powMonoidHom (p ^ (s - 1)) : H →* H).range ≤
      Nat.card (ggPowSubgroup U₁ hU₁ (p ^ (s - 1))) := by
    rw [← Subgroup.card_map_of_injective H.subtype_injective]
    apply Subgroup.card_le_of_le
    rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
    exact ⟨h, hHU₁ h.2, rfl⟩
  calc Nat.card B₁ ≤ p ^ (r + 1) := hB₁card
    _ = p * p ^ r := by ring
    _ ≤ p * Nat.card (ggPowSubgroup U₁ hU₁ (p ^ (s - 1))) :=
      Nat.mul_le_mul_left _ (hrange.trans hle)

theorem mem_of_commute_of_mem_thompson [Finite G] {U U₁ : Subgroup G}
    (hU₁ : U₁ ∈ thompsonAbelianSubgroups U) {c : G} (hcU : c ∈ U)
    (hc : ∀ u ∈ U₁, c * u = u * c) : c ∈ U₁ := by
  have hU₁H : U₁ ≤ Subgroup.closure ((U₁ : Set G) ∪ {c}) := fun u hu =>
    Subgroup.subset_closure (Or.inl hu)
  have hcH : c ∈ Subgroup.closure ((U₁ : Set G) ∪ {c}) :=
    Subgroup.subset_closure (Or.inr rfl)
  have hHU : Subgroup.closure ((U₁ : Set G) ∪ {c}) ≤ U :=
    (Subgroup.closure_le _).mpr (Set.union_subset hU₁.1 (Set.singleton_subset_iff.mpr hcU))
  have hcomm : ((U₁ : Set G) ∪ {c}).Pairwise Commute := by
    rintro a (ha | rfl) b (hb | rfl) -
    · exact congrArg Subtype.val (hU₁.2.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    · exact (hc a ha).symm
    · exact hc b hb
    · exact Commute.refl _
  have heq := Subgroup.eq_of_le_of_card_ge hU₁H
    (hU₁.2.2 _ hHU (Subgroup.isMulCommutative_closure hcomm))
  rw [heq]
  exact hcH

theorem normalizer_le_normalizer_ggPowSubgroup [Finite G] {U₁ : Subgroup G}
    (hU₁ : IsMulCommutative U₁) (n : ℕ) :
    Subgroup.normalizer (U₁ : Set G) ≤
      Subgroup.normalizer (ggPowSubgroup U₁ hU₁ n : Set G) := by
  intro m hm
  refine mem_normalizer_of_forall_conj_mem fun w hw => ?_
  obtain ⟨u, hu, rfl⟩ := hw
  have hu' : m⁻¹ * u * m ∈ U₁ := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hm) u).mp hu
    simpa using this
  refine ⟨_, hu', ?_⟩
  have h := conj_pow (a := m⁻¹) (b := u) (i := n)
  rw [inv_inv] at h
  exact h

end General

section Quadratic

variable {G : Type} [Group G]

theorem mem_of_quadratic_of_pow_mem [Finite G] {p n : ℕ} [Fact p.Prime]
    {B₁ U U₁ R : Subgroup G} (hU₁ab : IsMulCommutative U₁)
    (hB₁ : ∀ u : G, u ∈ B₁ ↔ u ∈ U₁ ∧ u ^ p = 1)
    (hW₀B₁ : ggPowSubgroup U₁ hU₁ab n ≤ B₁)
    (hcard : Nat.card B₁ ≤ p * Nat.card (ggPowSubgroup U₁ hU₁ab n))
    (hUC : U ≤ Subgroup.centralizer (B₁ : Set G)) (hUp : IsPGroup p U)
    (hUmax : ∀ Q : Subgroup G, Q ≤ Subgroup.centralizer (B₁ : Set G) → IsPGroup p Q → U ≤ Q →
      Q = U)
    (hNU : Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (U₁ : Set G))
    (hOp : GGOpAutTrivial p B₁)
    (hRp : IsPGroup p R) (hRM : R ≤ Subgroup.normalizer (B₁ : Set G)) (hUR : U ≤ R)
    {a : G} (haR : a ∈ R)
    (hq : ∀ u ∈ U₁, (u⁻¹ * (a⁻¹ * u * a)) * a = a * (u⁻¹ * (a⁻¹ * u * a)))
    (ha : a ^ n ∈ U₁) : a ∈ U := by
  set C := Subgroup.centralizer (B₁ : Set G) with hC
  set W₀ := ggPowSubgroup U₁ hU₁ab n with hW₀
  have hB₁U₁ : B₁ ≤ U₁ := fun b hb => ((hB₁ b).mp hb).1
  have hCN : C ≤ Subgroup.normalizer (B₁ : Set G) := Subgroup.centralizer_le_normalizer _
  have hRU : R ≤ Subgroup.normalizer (U : Set G) :=
    le_normalizer_of_maxPSubgroup (hRM.trans (ggNormalizer_le_normalizer_centralizer B₁)) hRp
      hUR hUC hUmax
  have hRC : R ⊓ C = U := hUmax _ inf_le_right (hRp.to_le inf_le_left) (le_inf hUR hUC)
  have haN : a ∈ Subgroup.normalizer (U₁ : Set G) := hNU (hRU haR)
  have hcomm : ∀ u ∈ U₁, ∀ v ∈ U₁, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hU₁ab.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hconjU₁ : ∀ u ∈ U₁, a⁻¹ * u * a ∈ U₁ := fun u hu => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haN) u).mp hu
    simpa using this
  have hδU₁ : ∀ u ∈ U₁, u⁻¹ * (a⁻¹ * u * a) ∈ U₁ := fun u hu =>
    U₁.mul_mem (U₁.inv_mem hu) (hconjU₁ u hu)
  have hW : ∀ w ∈ W₀, a⁻¹ * w * a = w := by
    rintro _ ⟨u, hu, rfl⟩
    have h1 := conj_pow_eq_mul_pow (hq u hu) n
    have h2 : (a ^ n)⁻¹ * u * a ^ n = u := by
      rw [mul_assoc, hcomm u hu _ ha, ← mul_assoc, inv_mul_cancel, one_mul]
    have hδ : (u⁻¹ * (a⁻¹ * u * a)) ^ n = 1 :=
      mul_left_cancel ((h1.symm.trans h2).trans (mul_one u).symm)
    have h3 := conj_pow (a := a⁻¹) (b := u) (i := n)
    rw [inv_inv] at h3
    have hc : Commute u (u⁻¹ * (a⁻¹ * u * a)) := hcomm u hu _ (hδU₁ u hu)
    calc a⁻¹ * u ^ n * a = (a⁻¹ * u * a) ^ n := h3.symm
      _ = (u * (u⁻¹ * (a⁻¹ * u * a))) ^ n := by rw [mul_inv_cancel_left]
      _ = u ^ n * (u⁻¹ * (a⁻¹ * u * a)) ^ n := hc.mul_pow n
      _ = u ^ n := by rw [hδ, mul_one]
  have hB₁p : IsPGroup p B₁ := fun b =>
    ⟨1, Subtype.ext (by simpa using ((hB₁ b).mp b.2).2)⟩
  have hδB : ∀ b ∈ B₁, b⁻¹ * (a⁻¹ * b * a) ∈ W₀ := by
    intro b hb
    set T : Subgroup G := B₁ ⊓ Subgroup.centralizer ({a} : Set G) with hT
    have hmemT : ∀ c ∈ B₁, a * c = c * a → c ∈ T := fun c hc hac =>
      ⟨hc, Subgroup.mem_centralizer_iff.mpr (by rintro _ rfl; exact hac)⟩
    have hW₀T : W₀ ≤ T := fun w hw => hmemT w (hW₀B₁ hw) (by
      calc a * w = a * (a⁻¹ * w * a) := by rw [hW w hw]
        _ = w * a := by group)
    have hδb : b⁻¹ * (a⁻¹ * b * a) ∈ T := by
      refine hmemT _ (B₁.mul_mem (B₁.inv_mem hb) ?_) (hq b (hB₁U₁ hb)).symm
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hRM haR)) b).mp hb
      simpa using this
    by_cases hTW : T = W₀
    · rw [← hTW]
      exact hδb
    · have hTB : T = B₁ :=
        eq_of_lt_of_card_le_mul hB₁p (lt_of_le_of_ne hW₀T (Ne.symm hTW)) inf_le_left hcard
      have hbT : b ∈ T := hTB ▸ hb
      have hab : a * b = b * a :=
        Subgroup.mem_centralizer_iff.mp hbT.2 a rfl
      have e : b⁻¹ * (a⁻¹ * b * a) = 1 := by
        calc b⁻¹ * (a⁻¹ * b * a) = b⁻¹ * (a⁻¹ * (b * a)) := by group
          _ = b⁻¹ * (a⁻¹ * (a * b)) := by rw [hab]
          _ = 1 := by group
      rw [e]
      exact W₀.one_mem
  have hCS : C ≤ ggFlagStab B₁ W₀ := by
    intro c hc
    have hcb : ∀ b ∈ B₁, c⁻¹ * b * c = b := fun b hb => by
      have h := Subgroup.mem_centralizer_iff.mp hc b hb
      calc c⁻¹ * b * c = c⁻¹ * (b * c) := by group
        _ = c⁻¹ * (c * b) := by rw [h]
        _ = b := by group
    refine ⟨hCN hc, fun b hb => ?_, fun w hw => hcb w (hW₀B₁ hw)⟩
    rw [hcb b hb, inv_mul_cancel]
    exact W₀.one_mem
  have hSC : ggFlagStab B₁ W₀ ≤ C := by
    refine hOp _ (fun g hg => hg.1) hCS ⟨fun g hg m => ?_⟩ (fun g hg => ⟨1, ?_⟩)
    · rw [Subgroup.mem_subgroupOf] at hg ⊢
      obtain ⟨c, hcC, hcm⟩ := exists_mul_mem_normalizer_of_maxPSubgroup
        (ggNormalizer_le_normalizer_centralizer B₁ m.2) hUp hUC hUmax
      have hm'B : c * (m : G) ∈ Subgroup.normalizer (B₁ : Set G) :=
        Subgroup.mul_mem _ (hCN hcC) m.2
      have hm'W : c * (m : G) ∈ Subgroup.normalizer (W₀ : Set G) :=
        normalizer_le_normalizer_ggPowSubgroup hU₁ab n (hNU hcm)
      have h1 := conj_mem_ggFlagStab hm'B hm'W hg
      have h2 := (ggFlagStab B₁ W₀).mul_mem
        ((ggFlagStab B₁ W₀).mul_mem ((ggFlagStab B₁ W₀).inv_mem (hCS hcC)) h1) (hCS hcC)
      have e : c⁻¹ * (c * (m : G) * (g : G) * (c * (m : G))⁻¹) * c =
          (m : G) * (g : G) * (m : G)⁻¹ := by group
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← e]
      exact h2
    · rw [pow_one]
      exact pow_mem_centralizer_of_mem_ggFlagStab
        (fun w hw => ((hB₁ w).mp (hW₀B₁ hw)).2) hg
  have haC : a ∈ C := hSC ⟨hRM haR, hδB, hW⟩
  rw [← hRC]
  exact ⟨haR, haC⟩

theorem conj_pow_eq_mul_pow_pow {p s : ℕ} (hs : 2 ≤ s) {U₁ : Subgroup G} {x' : G}
    (hexp : ∀ u ∈ U₁, u ^ p ^ s = 1)
    (hx' : ∀ u ∈ U₁, x'⁻¹ * u * x' = u ^ (1 + p ^ (s - 1))) (j : ℕ) :
    ∀ u ∈ U₁, (x' ^ j)⁻¹ * u * x' ^ j = u * (u ^ p ^ (s - 1)) ^ j := by
  have hNN : ∀ u ∈ U₁, u ^ (p ^ (s - 1) * p ^ (s - 1)) = 1 := by
    intro u hu
    have e : p ^ (s - 1) * p ^ (s - 1) = p ^ s * p ^ (s - 2) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    rw [e, pow_mul, hexp u hu, one_pow]
  induction j with
  | zero => intro u _; simp
  | succ j ih =>
    intro u hu
    have e : (x' ^ (j + 1))⁻¹ * u * x' ^ (j + 1) = x'⁻¹ * ((x' ^ j)⁻¹ * u * x' ^ j) * x' := by
      rw [pow_succ]
      group
    have hpow : ∀ (y : G) (k : ℕ), x'⁻¹ * y ^ k * x' = (x'⁻¹ * y * x') ^ k := by
      intro y k
      have h := conj_pow (a := x'⁻¹) (b := y) (i := k)
      rw [inv_inv] at h
      exact h.symm
    have e2 : x'⁻¹ * (u * (u ^ p ^ (s - 1)) ^ j) * x' =
        (x'⁻¹ * u * x') * (x'⁻¹ * (u ^ p ^ (s - 1)) ^ j * x') := by group
    rw [e, ih u hu, e2, hpow, hpow, hx' u hu]
    calc u ^ (1 + p ^ (s - 1)) * ((u ^ (1 + p ^ (s - 1))) ^ p ^ (s - 1)) ^ j
        = u ^ ((1 + p ^ (s - 1)) + (1 + p ^ (s - 1)) * p ^ (s - 1) * j) := by
          rw [← pow_mul, ← pow_mul, ← pow_add]
          congr 1
          ring
      _ = u ^ ((1 + p ^ (s - 1) * (j + 1)) + p ^ (s - 1) * p ^ (s - 1) * j) := by
          congr 1
          ring
      _ = u ^ (1 + p ^ (s - 1) * (j + 1)) := by
          rw [pow_add, pow_mul (u) (p ^ (s - 1) * p ^ (s - 1)), hNN u hu, one_pow, mul_one]
      _ = u * (u ^ p ^ (s - 1)) ^ (j + 1) := by
          rw [pow_add, pow_one, ← pow_mul]

theorem mem_of_quadratic [Finite G] {p s : ℕ} [Fact p.Prime] (hs : 2 ≤ s)
    {B₁ U U₁ R : Subgroup G} {x' : G} (hU₁ab : IsMulCommutative U₁)
    (hB₁ : ∀ u : G, u ∈ B₁ ↔ u ∈ U₁ ∧ u ^ p = 1)
    (hexp : ∀ u ∈ U₁, u ^ p ^ s = 1) (hord : ∃ u ∈ U₁, orderOf u = p ^ s)
    (hx' : ∀ u ∈ U₁, x'⁻¹ * u * x' = u ^ (1 + p ^ (s - 1))) (hx'p : x' ^ p = 1)
    (hcard : Nat.card B₁ ≤ p * Nat.card (ggPowSubgroup U₁ hU₁ab (p ^ (s - 1))))
    (hUC : U ≤ Subgroup.centralizer (B₁ : Set G)) (hUp : IsPGroup p U)
    (hUmax : ∀ Q : Subgroup G, Q ≤ Subgroup.centralizer (B₁ : Set G) → IsPGroup p Q → U ≤ Q →
      Q = U)
    (hJU : ∀ A ∈ thompsonAbelianSubgroups U, A = U₁) (hOp : GGOpAutTrivial p B₁)
    (hRp : IsPGroup p R) (hRM : R ≤ Subgroup.normalizer (B₁ : Set G)) (hUR : U ≤ R)
    (hΩ : ∀ w ∈ U, w ^ p ∈ U₁ → w ∈ Subgroup.zpowers x' ⊔ U₁)
    {a : G} (haR : a ∈ R)
    (hq : ∀ u ∈ U₁, (u⁻¹ * (a⁻¹ * u * a)) * a = a * (u⁻¹ * (a⁻¹ * u * a))) : a ∈ U := by
  have hp := (Fact.out : p.Prime)
  set N := p ^ (s - 1) with hNdef
  have hU₁mem : U₁ ∈ thompsonAbelianSubgroups U := mem_thompsonAbelianSubgroups_of_forall_eq hJU
  have hNU : Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (U₁ : Set G) :=
    normalizer_le_normalizer_of_forall_eq hJU
  have hRU : R ≤ Subgroup.normalizer (U : Set G) :=
    le_normalizer_of_maxPSubgroup (hRM.trans (ggNormalizer_le_normalizer_centralizer B₁)) hRp
      hUR hUC hUmax
  have hRC : R ⊓ Subgroup.centralizer (B₁ : Set G) = U :=
    hUmax _ inf_le_right (hRp.to_le inf_le_left) (le_inf hUR hUC)
  have hB₁U₁ : B₁ ≤ U₁ := fun b hb => ((hB₁ b).mp hb).1
  have hcomm : ∀ u ∈ U₁, ∀ v ∈ U₁, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hU₁ab.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hNp : N * p = p ^ s := by
    rw [hNdef, ← pow_succ]
    congr 1
    omega
  have hW₀B₁ : ggPowSubgroup U₁ hU₁ab N ≤ B₁ := by
    rintro _ ⟨u, hu, rfl⟩
    refine (hB₁ _).mpr ⟨U₁.pow_mem hu _, ?_⟩
    rw [← pow_mul, hNp]
    exact hexp u hu
  have hA₁ : ∀ g ∈ R, (∀ u ∈ U₁, (u⁻¹ * (g⁻¹ * u * g)) * g = g * (u⁻¹ * (g⁻¹ * u * g))) →
      g ^ N ∈ U₁ → g ∈ U := fun g hg hgq hgN =>
    mem_of_quadratic_of_pow_mem hU₁ab hB₁ hW₀B₁ hcard hUC hUp hUmax hNU hOp hRp hRM hUR hg hgq
      hgN
  have haN : a ∈ Subgroup.normalizer (U₁ : Set G) := hNU (hRU haR)
  have hconjU₁ : ∀ u ∈ U₁, a⁻¹ * u * a ∈ U₁ := fun u hu => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haN) u).mp hu
    simpa using this
  have hδU₁ : ∀ u ∈ U₁, u⁻¹ * (a⁻¹ * u * a) ∈ U₁ := fun u hu =>
    U₁.mul_mem (U₁.inv_mem hu) (hconjU₁ u hu)
  have hps : a ^ p ^ s ∈ U₁ := by
    have hc : ∀ u ∈ U₁, a ^ p ^ s * u = u * a ^ p ^ s := by
      intro u hu
      have h1 := conj_pow_eq_mul_pow (hq u hu) (p ^ s)
      rw [hexp _ (hδU₁ u hu), mul_one] at h1
      calc a ^ p ^ s * u = a ^ p ^ s * ((a ^ p ^ s)⁻¹ * u * a ^ p ^ s) := by rw [h1]
        _ = u * a ^ p ^ s := by group
    refine mem_of_commute_of_mem_thompson hU₁mem ?_ hc
    rw [← hRC]
    refine ⟨R.pow_mem haR _, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
    exact (hc b (hB₁U₁ hb)).symm
  by_contra haU
  set w := a ^ N with hwdef
  have hwR : w ∈ R := R.pow_mem haR N
  have hwconj : ∀ u ∈ U₁, w⁻¹ * u * w = u * (u⁻¹ * (a⁻¹ * u * a)) ^ N := fun u hu =>
    conj_pow_eq_mul_pow (hq u hu) N
  have hwq : ∀ u ∈ U₁, (u⁻¹ * (w⁻¹ * u * w)) * w = w * (u⁻¹ * (w⁻¹ * u * w)) := by
    intro u hu
    rw [hwconj u hu, inv_mul_cancel_left]
    exact ((Commute.pow_left (hq u hu) N).pow_right N).eq
  have hwN : w ^ N ∈ U₁ := by
    have e : N * N = p ^ s * p ^ (s - 2) := by
      rw [hNdef, ← pow_add, ← pow_add]
      congr 1
      omega
    rw [hwdef, ← pow_mul, e, pow_mul]
    exact U₁.pow_mem hps _
  have hwU : w ∈ U := hA₁ w hwR hwq hwN
  have hwU₁ : w ∉ U₁ := fun h => haU (hA₁ a haR hq h)
  have hwp : w ^ p ∈ U₁ := by
    rw [hwdef, ← pow_mul, hNp]
    exact hps
  have hx'N : Subgroup.zpowers x' ≤ Subgroup.normalizer (U₁ : Set G) := by
    rw [Subgroup.zpowers_le]
    refine mem_normalizer_of_forall_conj_mem fun u hu => ?_
    rw [hx' u hu]
    exact U₁.pow_mem hu _
  have hwS := hΩ w hwU hwp
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hx'N] at hwS
  obtain ⟨z, hz, u₀, hu₀, hzu⟩ := hwS
  replace hzu : z * u₀ = w := hzu
  obtain ⟨j, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hz)
  have hjact := conj_pow_eq_mul_pow_pow hs hexp hx' j
  have hδN : ∀ u ∈ U₁, (u⁻¹ * (a⁻¹ * u * a)) ^ N = (u ^ N) ^ j := by
    intro u hu
    have h1 := hwconj u hu
    have h2 : w⁻¹ * u * w = u * (u ^ N) ^ j := by
      rw [← hzu]
      have hv := hjact u hu
      have hvU₁ : (x' ^ j)⁻¹ * u * x' ^ j ∈ U₁ := by
        rw [hv]
        exact U₁.mul_mem hu (U₁.pow_mem (U₁.pow_mem hu _) _)
      have e : ((x' ^ j : G) * u₀)⁻¹ * u * ((x' ^ j : G) * u₀) =
          u₀⁻¹ * ((x' ^ j)⁻¹ * u * x' ^ j) * u₀ := by group
      rw [e, mul_assoc, hcomm _ hvU₁ u₀ hu₀, ← mul_assoc, inv_mul_cancel, one_mul, hv]
    exact mul_left_cancel (h1.symm.trans h2)
  obtain ⟨u₁, hu₁, hou₁⟩ := hord
  set v := u₁⁻¹ * (a⁻¹ * u₁ * a) with hvdef
  have hvU₁ : v ∈ U₁ := hδU₁ u₁ hu₁
  have hδv : v⁻¹ * (a⁻¹ * v * a) = 1 := by
    have h := hq u₁ hu₁
    calc v⁻¹ * (a⁻¹ * v * a) = v⁻¹ * (a⁻¹ * (v * a)) := by group
      _ = v⁻¹ * (a⁻¹ * (a * v)) := by rw [h]
      _ = 1 := by group
  have h1 := hδN v hvU₁
  rw [hδv, one_pow, hδN u₁ hu₁, ← pow_mul, ← pow_mul] at h1
  have hdvd : p ^ s ∣ N * (j * j) := hou₁ ▸ orderOf_dvd_of_pow_eq_one h1.symm
  have hpj : p ∣ j * j := by
    rw [← hNp] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos _) hdvd
  obtain ⟨t, rfl⟩ := (hp.dvd_mul.mp hpj).elim id id
  apply hwU₁
  rw [← hzu, pow_mul, hx'p, one_pow, one_mul]
  exact hu₀

theorem mem_zpowers_sup_of_cyclic [Finite G] {p : ℕ} [Fact p.Prime] {U U₁ : Subgroup G} {g x : G}
    (hUN : U ≤ Subgroup.normalizer (U₁ : Set G)) (hgU : g ∈ U)
    (hcyc : U ≤ Subgroup.zpowers g ⊔ U₁) (hxU : x ∈ U) (hxU₁ : x ∉ U₁) (hxp : x ^ p = 1)
    {w : G} (hwU : w ∈ U) (hwp : w ^ p ∈ U₁) : w ∈ Subgroup.zpowers x ⊔ U₁ := by
  have hnorm : (U₁.subgroupOf U).Normal := ⟨fun a ha b => by
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hUN b.2) a).mp ha⟩
  let π : ↥U →* ↥U ⧸ U₁.subgroupOf U := QuotientGroup.mk' _
  have hπ : ∀ u v : ↥U, π u = π v ↔ (u : G)⁻¹ * v ∈ U₁ := fun u v => by
    simp only [π, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf,
      Subgroup.coe_mul, Subgroup.coe_inv]
  have hgN : Subgroup.zpowers g ≤ Subgroup.normalizer (U₁ : Set G) :=
    Subgroup.zpowers_le.mpr (hUN hgU)
  have hQcyc : IsCyclic (↥U ⧸ U₁.subgroupOf U) := by
    refine ⟨π ⟨g, hgU⟩, fun q => ?_⟩
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (U₁.subgroupOf U) q
    have hu := hcyc u.2
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hgN] at hu
    obtain ⟨z, hz, u₁, hu₁, hzu⟩ := hu
    replace hzu : z * u₁ = u := hzu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    refine ⟨k, ?_⟩
    change π ⟨g, hgU⟩ ^ k = π u
    rw [← map_zpow, hπ]
    simp only [Subgroup.coe_zpow]
    rw [← hzu, inv_mul_cancel_left]
    exact hu₁
  have hxQ : π ⟨x, hxU⟩ ≠ 1 := by
    rw [← map_one π, Ne, hπ]
    simpa using hxU₁
  by_cases hw1 : π ⟨w, hwU⟩ = 1
  · rw [← map_one π, hπ] at hw1
    have hw : w ∈ U₁ := by simpa using hw1
    exact Subgroup.mem_sup_right hw
  · have hxo : orderOf (π ⟨x, hxU⟩) = p := by
      refine orderOf_eq_prime ?_ hxQ
      rw [← map_pow]
      have : (⟨x, hxU⟩ : ↥U) ^ p = 1 := Subtype.ext (by simpa using hxp)
      rw [this, map_one]
    have hwo : orderOf (π ⟨w, hwU⟩) = p := by
      refine orderOf_eq_prime ?_ hw1
      rw [← map_pow, ← map_one π, hπ]
      simpa using hwp
    have heq : Subgroup.zpowers (π ⟨w, hwU⟩) = Subgroup.zpowers (π ⟨x, hxU⟩) :=
      IsCyclic.subgroup_eq_iff_card_eq.mpr (by rw [Nat.card_zpowers, Nat.card_zpowers, hxo, hwo])
    have hmem : π ⟨w, hwU⟩ ∈ Subgroup.zpowers (π ⟨x, hxU⟩) := heq ▸ Subgroup.mem_zpowers _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← map_zpow, hπ] at hk
    simp only [Subgroup.coe_zpow] at hk
    have e : w = x ^ k * ((x ^ k)⁻¹ * w) := by group
    rw [e]
    exact Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers x k) hk

end Quadratic

@[expose] def GGUModUOneCyclicInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁ → GGL46 p Bs x X U U₁ →
      ∃ g ∈ U, U ≤ Subgroup.zpowers g ⊔ U₁

@[expose] def GGL47OmegaInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁ → GGL46 p Bs x X U U₁ →
      ∀ w ∈ U, w ^ p ∈ U₁ → w ∈ Subgroup.zpowers x ⊔ U₁

section Main

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem not_mem_of_ggL46 {p : ℕ} [Fact p.Prime] {Bs X U U₁ : Subgroup G} {x : G}
    (h46 : GGL46 p Bs x X U U₁) : x ∉ U₁ := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨hab, ⟨s, hs, -, ⟨u₁, hu₁, hou₁⟩, ⟨x', hx'x, hx'⟩, -⟩, -⟩ := h46
  intro hxU₁
  have hx'U₁ : x' ∈ U₁ := by
    have h : x' ∈ Subgroup.zpowers x := hx'x ▸ Subgroup.mem_zpowers x'
    exact Subgroup.zpowers_le.mpr hxU₁ h
  have hc : x'⁻¹ * u₁ * x' = u₁ := by
    have h := congrArg Subtype.val (hab.is_comm.comm ⟨u₁, hu₁⟩ ⟨x', hx'U₁⟩)
    simp only [Subgroup.coe_mul] at h
    rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [hx' u₁ hu₁, pow_add, pow_one] at hc
  have h1 : u₁ ^ p ^ (s - 1) = 1 := mul_left_cancel (hc.trans (mul_one u₁).symm)
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [hou₁, Nat.pow_dvd_pow_iff_le_right hp.one_lt] at h2
  omega

theorem ggL47Input_of_omega (hΩ : GGL47OmegaInput) : GGL47Input := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hS h46 R hRp hRM _ hUR A hA hAAA
  have hcfg := hS.1.1
  have : Fact p.Prime := ⟨hcfg.1.2.2.2.2.2.1.1⟩
  have hp := (Fact.out : p.Prime)
  have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hcfg.1.2.2.2.2.2.2.1.2.1
  have hxp : x ^ p = 1 := hBs.2 x hxBs
  obtain ⟨hUC, hUp, hUmax, -⟩ := hS.2.2.2.2.2.2.1
  have hΩw := hΩ G p B Bs x L D J X B₂ d y K U U₁ hS h46
  obtain ⟨hab, ⟨s, hs, hexp, hord, ⟨x', hx'x, hx'⟩, H, r, hHU₁, -, hHcard, hHB₁, hB₁card⟩, hJU,
    hΩ₁, -, hOp⟩ := h46
  have hx'p : x' ^ p = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hx'x ▸ Subgroup.mem_zpowers x')
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
  have hcard := card_le_mul_card_ggPowSubgroup hp (by omega) hab hΩ₁ hHU₁ hHcard hHB₁ hB₁card
  have hΩ' : ∀ w ∈ U, w ^ p ∈ U₁ → w ∈ Subgroup.zpowers x' ⊔ U₁ := fun w hw hwp => by
    rw [hx'x]
    exact hΩw w hw hwp
  intro a ha
  refine mem_of_quadratic hs hab hΩ₁ hexp hord hx' hx'p hcard hUC hUp hUmax hJU hOp hRp hRM hUR
    hΩ' (hA.1 ha) fun u hu => ?_
  have hc : ⁅⁅u⁻¹, a⁻¹⁆, a⁆ ∈ ⁅⁅U₁, A⁆, A⁆ :=
    Subgroup.commutator_mem_commutator
      (Subgroup.commutator_mem_commutator (U₁.inv_mem hu) (A.inv_mem ha)) ha
  rw [hAAA, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
  have e : u⁻¹ * (a⁻¹ * u * a) = ⁅u⁻¹, a⁻¹⁆ := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact hc

theorem ggL47OmegaInput_of_cyclic (hcyc : GGUModUOneCyclicInput) : GGL47OmegaInput := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hS h46 w hwU hwp
  have hcfg := hS.1.1
  have : Fact p.Prime := ⟨hcfg.1.2.2.2.2.2.1.1⟩
  have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hcfg.1.2.2.2.2.2.2.1.2.1
  obtain ⟨g, hgU, hU⟩ := hcyc G p B Bs x L D J X B₂ d y K U U₁ hS h46
  have hUN : U ≤ Subgroup.normalizer (U₁ : Set G) :=
    (Subgroup.le_normalizer).trans (normalizer_le_normalizer_of_forall_eq h46.2.2.1)
  exact mem_zpowers_sup_of_cyclic hUN hgU hU (hS.2.2.2.2.2.2.1.2.2.2 hxBs)
    (not_mem_of_ggL46 h46) (hBs.2 x hxBs) hwU hwp

theorem ggL47Input_of_cyclic (hcyc : GGUModUOneCyclicInput) : GGL47Input :=
  ggL47Input_of_omega (ggL47OmegaInput_of_cyclic hcyc)

end Main

end CFSG.StandardType

end
