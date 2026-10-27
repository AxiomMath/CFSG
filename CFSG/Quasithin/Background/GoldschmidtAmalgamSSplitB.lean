module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamSGlobB
public import CFSG.Quasithin.Background.GoldschmidtAmalgamSTypeB

public section

namespace CFSG.Quasithin.F6.GoldAmS

open Equiv CFSG.Open CFSG.QuasithinUnique

theorem exists_split_hom {E : Type*} [Group E] (A T : Subgroup E) (hTA : T ≤ A)
    (hidx : (T.subgroupOf A).index = 3) {ε : E} (hε : ε ∈ T) (hεc : ∀ g ∈ A, g * ε = ε * g)
    (hε2 : ε * ε = 1) (φ : ↥T →* Multiplicative (ZMod 2))
    (hφ : φ ⟨ε, hε⟩ = Multiplicative.ofAdd 1) :
    ∃ V : ↥A →* Multiplicative (ZMod 2), V ⟨ε, hTA hε⟩ = Multiplicative.ofAdd 1 := by
  classical
  let T' : Subgroup ↥A := T.subgroupOf A
  have : T'.FiniteIndex := ⟨by rw [show T'.index = 3 from hidx]; norm_num⟩
  let φ' : ↥T' →* Multiplicative (ZMod 2) :=
    φ.comp (Subgroup.subgroupOfEquivOfLe hTA).toMonoidHom
  refine ⟨MonoidHom.transfer φ', ?_⟩
  let ε' : ↥A := ⟨ε, hTA hε⟩
  have hε'T : ε' ∈ T' := hε
  have key : ∀ (k : ℕ) (g₀ : ↥A), g₀⁻¹ * ε' ^ k * g₀ ∈ T' → g₀⁻¹ * ε' ^ k * g₀ = ε' ^ k := by
    intro k g₀ _
    have hc : Commute g₀ ε' := Subtype.ext (hεc g₀.1 g₀.2)
    have hc' : Commute g₀⁻¹ (ε' ^ k) := (hc.pow_right k).inv_left
    calc g₀⁻¹ * ε' ^ k * g₀ = ε' ^ k * g₀⁻¹ * g₀ := by rw [hc'.eq]
      _ = ε' ^ k := by group
  refine (MonoidHom.transfer_eq_pow φ' ε' key).trans ?_
  have h3 : ε' ^ T'.index = ε' := by
    rw [show T'.index = 3 from hidx]
    apply Subtype.ext
    show ε ^ 3 = ε
    rw [pow_three, hε2, mul_one]
  have hT : ∀ hmem : ε' ^ T'.index ∈ T', (⟨ε' ^ T'.index, hmem⟩ : ↥T') = ⟨ε', hε'T⟩ :=
    fun hmem => Subtype.ext h3
  rw [hT]
  exact hφ

section Complement

variable {E : Type*} [Group E]

def complSub (T N : Subgroup E) (b : E) (hbb : b * b = 1)
    (hN : ∀ n ∈ N, b * n * b⁻¹ ∈ N) : Subgroup E where
  carrier := {t | t ∈ T ∧ (t ∈ N ∨ t * b ∈ N)}
  one_mem' := ⟨T.one_mem, Or.inl N.one_mem⟩
  mul_mem' := by
    have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
    have hN' : ∀ n ∈ N, b⁻¹ * n * b ∈ N := by
      intro n hn
      have := hN n hn
      rw [hbi] at this ⊢
      exact this
    rintro t s ⟨htT, ht⟩ ⟨hsT, hs⟩
    refine ⟨T.mul_mem htT hsT, ?_⟩
    rcases ht with ht | ht <;> rcases hs with hs | hs
    · exact Or.inl (N.mul_mem ht hs)
    · exact Or.inr (by rw [mul_assoc]; exact N.mul_mem ht hs)
    · right
      have : t * s * b = (t * b) * (b⁻¹ * s * b) := by group
      rw [this]
      exact N.mul_mem ht (hN' s hs)
    · left
      have : t * s = (t * b) * (b * (s * b) * b⁻¹) := by
        calc t * s = t * (b * b) * s * (b * b⁻¹) := by rw [hbb]; group
          _ = (t * b) * (b * (s * b) * b⁻¹) := by group
      rw [this]
      exact N.mul_mem ht (hN (s * b) hs)
  inv_mem' := by
    have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
    rintro t ⟨htT, ht⟩
    refine ⟨T.inv_mem htT, ?_⟩
    rcases ht with ht | ht
    · exact Or.inl (N.inv_mem ht)
    · right
      have : t⁻¹ * b = b * (t * b)⁻¹ * b⁻¹ := by
        calc t⁻¹ * b = t⁻¹ * b⁻¹ := by rw [hbi]
          _ = b * (t * b)⁻¹ * b⁻¹ := by group
      rw [this]
      exact hN _ (N.inv_mem ht)

end Complement

section Vertex

variable {E : Type*} [Group E] [Finite E] {A₁ A₂ N₁ N₂ : Subgroup E} {ε₁ ε₂ : E}
  (G : Glob A₁ A₂ N₁ N₂ ε₁ ε₂)

include G

omit [Finite E] in
theorem Glob.card_T_eq : Nat.card ↥(A₁ ⊓ A₂) = 2 * Nat.card ↥(pCoreOf 2 A₁) := by
  rw [G.card, G.v₁.Q_card]

theorem Glob.exists_V₁ {a b : E} (haN : a ∈ N₁) (hbQ : b ∈ pCoreOf 2 A₂)
    (hb1 : b ∉ pCoreOf 2 A₁) :
    ∃ V : ↥A₁ →* Multiplicative (ZMod 2),
      V ⟨ε₁, G.v₁.Q_le G.v₁.ε_mem⟩ = Multiplicative.ofAdd 1 ∧
      V ⟨a, G.v₁.Q_le (G.v₁.N_le haN)⟩ = 1 ∧ V ⟨b, (G.Q₂_le_inf hbQ).1⟩ = 1 := by
  have hbT : b ∈ A₁ ⊓ A₂ := G.Q₂_le_inf hbQ
  have hbb : b * b = 1 := G.v₂.Q_exp b hbQ
  have hbA : b ∈ A₁ := hbT.1
  let H : Subgroup E := complSub (A₁ ⊓ A₂) N₁ b hbb (fun n hn => G.v₁.N_norm b hbA n hn)
  have hP : ProdStr (A₁ ⊓ A₂) H ε₁ :=
    { le := fun t ht => ht.1
      mem := G.ε₁_mem_inf
      sq := G.v₁.Q_exp ε₁ G.v₁.ε_mem
      central := fun g hg => G.v₁.ε_central g hg.1
      not_mem := by
        rintro ⟨_, h | h⟩
        · exact G.v₁.ε_not_N h
        · apply hb1
          have : b = ε₁⁻¹ * (ε₁ * b) := by group
          rw [this]
          exact Subgroup.mul_mem _ (Subgroup.inv_mem _ G.v₁.ε_mem) (G.v₁.N_le h)
      split := by
        intro g hg
        rcases mem_or_mul_mem_of_card (K := pCoreOf 2 A₁) (A := A₁ ⊓ A₂) G.Q₁_le_inf G.card_T_eq
            hbT hb1 hg with h | h
        · rcases G.v₁.Q_split g h with h' | h'
          · exact Or.inl ⟨hg, Or.inl h'⟩
          · exact Or.inr ⟨Subgroup.mul_mem _ G.ε₁_mem_inf hg, Or.inl h'⟩
        · rcases G.v₁.Q_split (g * b) h with h' | h'
          · exact Or.inl ⟨hg, Or.inr h'⟩
          · exact Or.inr ⟨Subgroup.mul_mem _ G.ε₁_mem_inf hg,
              Or.inr (by rw [mul_assoc]; exact h')⟩ }
  let φ : ↥(A₁ ⊓ A₂) →* Multiplicative (ZMod 2) :=
    (MonoidHom.fst _ _).comp hP.iota.symm.toMonoidHom
  have hφ : φ ⟨ε₁, G.ε₁_mem_inf⟩ = Multiplicative.ofAdd 1 := by
    have h1 : hP.iota.symm ⟨ε₁, G.ε₁_mem_inf⟩ = (Multiplicative.ofAdd 1, 1) :=
      (MulEquiv.symm_apply_eq _).2 hP.iota_apply_eps.symm
    show (hP.iota.symm ⟨ε₁, G.ε₁_mem_inf⟩).1 = _
    rw [h1]
  have hidx : ((A₁ ⊓ A₂).subgroupOf A₁).index = 3 :=
    G.amalgam.toIsGoldschmidtTriple.relIndex_inf_left
  obtain ⟨V₀, hV₀⟩ := exists_split_hom A₁ (A₁ ⊓ A₂) inf_le_left hidx G.ε₁_mem_inf
    G.v₁.ε_central (G.v₁.Q_exp ε₁ G.v₁.ε_mem) φ hφ
  obtain ⟨s, hs1, hs2⟩ := G.v₁.sign
  by_cases hVb : V₀ ⟨b, hbA⟩ = 1
  · exact ⟨V₀, hV₀, G.v₁.N_kill V₀ a haN, hVb⟩
  · refine ⟨V₀ * s, ?_, ?_, ?_⟩
    · show V₀ ⟨ε₁, _⟩ * s ⟨ε₁, _⟩ = _
      rw [hV₀, hs1 ε₁ G.v₁.ε_mem, mul_one]
    · show V₀ ⟨a, _⟩ * s ⟨a, _⟩ = 1
      rw [G.v₁.N_kill V₀ a haN, hs1 a (G.v₁.N_le haN), mul_one]
    · show V₀ ⟨b, _⟩ * s ⟨b, _⟩ = 1
      have h1 : V₀ ⟨b, hbA⟩ = Multiplicative.ofAdd 1 := (ProdStr.zmod_cases _).resolve_left hVb
      rw [h1, hs2 b hbA hbb hb1]
      decide

end Vertex

section Assembly

variable {E : Type*} [Group E] {A₁ A₂ N₁ N₂ : Subgroup E} {ε₁ ε₂ : E}

theorem hom_mul_sub {A : Subgroup E} {M : Type*} [Group M] (V : ↥A →* M) {x y : E}
    (hx : x ∈ A) (hy : y ∈ A) : V ⟨x * y, A.mul_mem hx hy⟩ = V ⟨x, hx⟩ * V ⟨y, hy⟩ := by
  rw [← map_mul]
  rfl

theorem mem_ker_map {A : Subgroup E} (V : ↥A →* Multiplicative (ZMod 2)) {x : E} :
    x ∈ V.ker.map A.subtype ↔ ∃ h : x ∈ A, V ⟨x, h⟩ = 1 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hV⟩
    exact ⟨⟨x, h⟩, hV, rfl⟩

theorem vertexA_of_split {A Q N : Subgroup E} {ε : E} (v : VtxB A Q N ε) {K : Subgroup E}
    (hK : ProdStr A K ε) (hA : Nat.card ↥A = 48) : VertexA K (K ⊓ Q) := by
  have hQ := hK.inf_right v.Q_le v.ε_mem
  have h1 := hQ.card_eq
  have h2 := hK.card_eq
  rw [v.Q_card] at h1
  refine ⟨inf_le_left, ?_, by omega, by omega, fun q hq => v.Q_exp q hq.2, ?_⟩
  · intro g hg q hq
    exact ⟨K.mul_mem (K.mul_mem hg hq.1) (K.inv_mem hg), v.Q_norm g (hK.le hg) q hq.2⟩
  · intro g hg hc
    have hgA := hK.le hg
    have hgQ : g ∈ Q := v.cent g hgA fun q hq => by
      rcases hQ.split q hq with h | h
      · exact hc q h
      · have := hc _ h
        have hce : g * ε = ε * g := v.ε_central g hgA
        apply mul_left_cancel (a := ε)
        calc ε * (g * q) = ε * g * q := by group
          _ = g * ε * q := by rw [hce]
          _ = g * (ε * q) := by group
          _ = ε * q * g := this
          _ = ε * (q * g) := by group
    exact ⟨hg, hgQ⟩

theorem Glob.symm (G : Glob A₁ A₂ N₁ N₂ ε₁ ε₂) : Glob A₂ A₁ N₂ N₁ ε₂ ε₁ where
  amalgam := ⟨G.amalgam.toIsGoldschmidtTriple.symm, G.amalgam.pCore_eq_bot⟩
  card := by rw [inf_comm]; exact G.card
  v₁ := G.v₂
  v₂ := G.v₁

variable [Finite E] (G : Glob A₁ A₂ N₁ N₂ ε₁ ε₂)

include G

theorem Glob.V_agree {a b : E} (haN : a ∈ N₁) (ha2 : a ∉ pCoreOf 2 A₂) (hbN : b ∈ N₂)
    (hb1 : b ∉ pCoreOf 2 A₁) (hzN₁ : ε₁ * ε₂ ∈ N₁) (hzN₂ : ε₁ * ε₂ ∈ N₂)
    (V₁ : ↥A₁ →* Multiplicative (ZMod 2)) (V₂ : ↥A₂ →* Multiplicative (ZMod 2))
    (h₁ε : V₁ ⟨ε₁, G.v₁.Q_le G.v₁.ε_mem⟩ = Multiplicative.ofAdd 1)
    (h₁b : V₁ ⟨b, (G.Q₂_le_inf (G.v₂.N_le hbN)).1⟩ = 1)
    (h₂ε : V₂ ⟨ε₂, G.v₂.Q_le G.v₂.ε_mem⟩ = Multiplicative.ofAdd 1)
    (h₂a : V₂ ⟨a, (G.Q₁_le_inf (G.v₁.N_le haN)).2⟩ = 1) :
    ∀ (t : E) (ht : t ∈ A₁ ⊓ A₂), V₁ ⟨t, ht.1⟩ = V₂ ⟨t, ht.2⟩ := by
  have hzT : ε₁ * ε₂ ∈ A₁ ⊓ A₂ := Subgroup.mul_mem _ G.ε₁_mem_inf G.ε₂_mem_inf
  have hzQ₁ : ε₁ * ε₂ ∈ pCoreOf 2 A₁ := Subgroup.mul_mem _ G.v₁.ε_mem G.ε₂_mem_Q₁
  have hzQ₂ : ε₁ * ε₂ ∈ pCoreOf 2 A₂ := Subgroup.mul_mem _ G.ε₁_mem_Q₂ G.v₂.ε_mem
  have hzz : (ε₁ * ε₂) * (ε₁ * ε₂) = 1 := G.v₁.Q_exp _ hzQ₁
  have hzV₂ : V₂ ⟨ε₁ * ε₂, hzT.2⟩ = 1 := G.v₂.N_kill V₂ _ hzN₂
  have hε₁V₂ : V₂ ⟨ε₁, G.ε₁_mem_inf.2⟩ = Multiplicative.ofAdd 1 := by
    have e : (⟨ε₁, G.ε₁_mem_inf.2⟩ : ↥A₂) =
        ⟨ε₁ * ε₂, hzT.2⟩ * ⟨ε₂, G.v₂.Q_le G.v₂.ε_mem⟩ :=
      Subtype.ext (by
        show ε₁ = ε₁ * ε₂ * ε₂
        rw [mul_assoc, G.v₂.Q_exp ε₂ G.v₂.ε_mem, mul_one])
    rw [e, map_mul, hzV₂, h₂ε, one_mul]
  have hN₁V₂ : ∀ (n : E) (hn : n ∈ N₁), V₂ ⟨n, (G.Q₁_le_inf (G.v₁.N_le hn)).2⟩ = 1 := by
    have hcard : Nat.card N₁ ≤ 4 := G.v₁.N_card.le
    have hza : a * (ε₁ * ε₂) ∈ N₁ := Subgroup.mul_mem _ haN hzN₁
    have haz2 : a ≠ ε₁ * ε₂ := fun h => ha2 (h ▸ hzQ₂)
    have key := mem_of_card_le_four hcard (u := a) (v := ε₁ * ε₂) (w := a * (ε₁ * ε₂))
      haN hzN₁ hza (fun h => ha2 (h ▸ Subgroup.one_mem _)) (Ne.symm G.z_ne_one)
      (by
        intro h
        apply haz2
        have h1 : a⁻¹ = ε₁ * ε₂ := by
          have : a * (ε₁ * ε₂) = 1 := h.symm
          calc a⁻¹ = a⁻¹ * (a * (ε₁ * ε₂)) := by rw [this, mul_one]
            _ = ε₁ * ε₂ := by group
        have h2 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (G.v₁.Q_exp a (G.v₁.N_le haN))
        rw [← h2, h1])
      haz2
      (by
        intro h
        apply G.z_ne_one
        have : a * (ε₁ * ε₂) = a * 1 := by rw [mul_one]; exact h.symm
        exact mul_left_cancel this)
      (by
        intro h
        apply (fun (h' : a = 1) => ha2 (h' ▸ Subgroup.one_mem _))
        have : (1 : E) * (ε₁ * ε₂) = a * (ε₁ * ε₂) := by rw [one_mul]; exact h
        exact (mul_right_cancel this).symm)
    intro n hn
    rcases key n hn with h | h | h | h
    · subst h
      have : (⟨1, _⟩ : ↥A₂) = 1 := rfl
      rw [this, map_one]
    · subst h
      exact h₂a
    · subst h
      exact hzV₂
    · subst h
      rw [hom_mul_sub V₂ (G.Q₁_le_inf (G.v₁.N_le haN)).2 hzT.2, h₂a, hzV₂, one_mul]
  have hQ : ∀ (q : E) (hq : q ∈ pCoreOf 2 A₁),
      V₁ ⟨q, G.v₁.Q_le hq⟩ = V₂ ⟨q, (G.Q₁_le_inf hq).2⟩ := by
    intro q hq
    rcases G.v₁.Q_split q hq with h | h
    · rw [G.v₁.N_kill V₁ q h, hN₁V₂ q h]
    · have e1 : (⟨q, G.v₁.Q_le hq⟩ : ↥A₁) =
          ⟨ε₁, G.v₁.Q_le G.v₁.ε_mem⟩ * ⟨ε₁ * q, G.v₁.Q_le (G.v₁.N_le h)⟩ :=
        Subtype.ext (by
          show q = ε₁ * (ε₁ * q)
          rw [← mul_assoc, G.v₁.Q_exp ε₁ G.v₁.ε_mem, one_mul])
      have e2 : (⟨q, (G.Q₁_le_inf hq).2⟩ : ↥A₂) =
          ⟨ε₁, G.ε₁_mem_inf.2⟩ * ⟨ε₁ * q, (G.Q₁_le_inf (G.v₁.N_le h)).2⟩ :=
        Subtype.ext (by
          show q = ε₁ * (ε₁ * q)
          rw [← mul_assoc, G.v₁.Q_exp ε₁ G.v₁.ε_mem, one_mul])
      rw [e1, e2, map_mul, map_mul, h₁ε, hε₁V₂, G.v₁.N_kill V₁ _ h, hN₁V₂ _ h]
  intro t ht
  have hbT : b ∈ A₁ ⊓ A₂ := G.Q₂_le_inf (G.v₂.N_le hbN)
  have hbb : b * b = 1 := G.v₂.Q_exp b (G.v₂.N_le hbN)
  have hV₂b : V₂ ⟨b, hbT.2⟩ = 1 := G.v₂.N_kill V₂ b hbN
  rcases mem_or_mul_mem_of_card (K := pCoreOf 2 A₁) (A := A₁ ⊓ A₂) G.Q₁_le_inf G.card_T_eq
      hbT hb1 ht with h | h
  · exact hQ t h
  · have e1 : (⟨t, ht.1⟩ : ↥A₁) = ⟨t * b, Subgroup.mul_mem _ ht.1 hbT.1⟩ * ⟨b, hbT.1⟩ :=
      Subtype.ext (by
        show t = t * b * b
        rw [mul_assoc, hbb, mul_one])
    have e2 : (⟨t, ht.2⟩ : ↥A₂) = ⟨t * b, Subgroup.mul_mem _ ht.2 hbT.2⟩ * ⟨b, hbT.2⟩ :=
      Subtype.ext (by
        show t = t * b * b
        rw [mul_assoc, hbb, mul_one])
    rw [e1, e2, map_mul, map_mul, h₁b, hV₂b, mul_one, mul_one]
    exact hQ (t * b) h

theorem Glob.typeB : Nonempty (TypeBData A₁ A₂) := by
  obtain ⟨a, b, haN, ha2, hbN, hb1, hab, hz, hzN₁, hzN₂⟩ := G.exists_z
  have hbQ : b ∈ pCoreOf 2 A₂ := G.v₂.N_le hbN
  have haQ : a ∈ pCoreOf 2 A₁ := G.v₁.N_le haN
  obtain ⟨V₁, hV₁ε, hV₁a, hV₁b⟩ := G.exists_V₁ haN hbQ hb1
  obtain ⟨V₂, hV₂ε, hV₂b, hV₂a⟩ := G.symm.exists_V₁ hbN haQ ha2
  have hag := G.V_agree haN ha2 hbN hb1 hzN₁ hzN₂ V₁ V₂ hV₁ε hV₁b hV₂ε hV₂a
  have prod₁ : ProdStr A₁ (V₁.ker.map A₁.subtype) ε₁ :=
    ProdStr.of_hom A₁ (G.v₁.Q_le G.v₁.ε_mem) (G.v₁.Q_exp ε₁ G.v₁.ε_mem) G.v₁.ε_central V₁ hV₁ε
  have prod₂ : ProdStr A₂ (V₂.ker.map A₂.subtype) ε₂ :=
    ProdStr.of_hom A₂ (G.v₂.Q_le G.v₂.ε_mem) (G.v₂.Q_exp ε₂ G.v₂.ε_mem) G.v₂.ε_central V₂ hV₂ε
  set K₁ : Subgroup E := V₁.ker.map A₁.subtype with hK₁
  set K₂ : Subgroup E := V₂.ker.map A₂.subtype with hK₂
  have hA₁ : Nat.card ↥A₁ = 48 := by
    rw [card_vertex_left G.amalgam.toIsGoldschmidtTriple, G.card]
  have hA₂ : Nat.card ↥A₂ = 48 := by
    rw [card_vertex_left G.amalgam.toIsGoldschmidtTriple.symm, inf_comm, G.card]
  have hKT : ∀ t (ht : t ∈ A₁ ⊓ A₂), t ∈ K₁ ↔ t ∈ K₂ := by
    intro t ht
    rw [hK₁, hK₂, mem_ker_map, mem_ker_map]
    constructor
    · rintro ⟨h, hv⟩
      exact ⟨ht.2, by rw [← hag t ht]; exact hv⟩
    · rintro ⟨h, hv⟩
      exact ⟨ht.1, by rw [hag t ht]; exact hv⟩
  have hinf : K₁ ⊓ K₂ = K₁ ⊓ (A₁ ⊓ A₂) := by
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, prod₁.le h1, prod₂.le h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (hKT x h2).1 h1⟩
  have hTprod : ProdStr (A₁ ⊓ A₂) (K₁ ⊓ (A₁ ⊓ A₂)) ε₁ := prod₁.inf_right inf_le_left G.ε₁_mem_inf
  have hH : Nat.card ↥(K₁ ⊓ K₂) = 8 := by
    have := hTprod.card_eq
    rw [G.card] at this
    rw [hinf]
    omega
  have hvA₁ := vertexA_of_split G.v₁ prod₁ hA₁
  have hvA₂ := vertexA_of_split G.v₂ prod₂ hA₂
  have hzA₁ : ε₁ * ε₂ ∈ A₁ := G.v₁.Q_le (G.v₁.N_le hzN₁)
  have hzA₂ : ε₁ * ε₂ ∈ A₂ := G.v₂.Q_le (G.v₂.N_le hzN₂)
  have hzK₁ : ε₁ * ε₂ ∈ K₁ := (mem_ker_map V₁).2 ⟨hzA₁, G.v₁.N_kill V₁ _ hzN₁⟩
  have hzK₂ : ε₁ * ε₂ ∈ K₂ := (mem_ker_map V₂).2 ⟨hzA₂, G.v₂.N_kill V₂ _ hzN₂⟩
  have haK₁ : a ∈ K₁ := (mem_ker_map V₁).2 ⟨G.v₁.Q_le haQ, G.v₁.N_kill V₁ _ haN⟩
  have typeA : TypeA K₁ K₂ := by
    refine ⟨K₁ ⊓ pCoreOf 2 A₁, K₂ ⊓ pCoreOf 2 A₂, hvA₁, hvA₂, ?_, ?_, hH⟩
    · intro x hx
      exact (hKT x (G.Q₁_le_inf hx.2)).1 hx.1
    · intro h
      have : a ∈ K₂ ⊓ pCoreOf 2 A₂ := h ▸ ⟨haK₁, haQ⟩
      exact ha2 this.2
  refine ⟨⟨K₁, K₂, ε₁, ε₂, prod₁, prod₂, typeA, G.ε₁_mem_inf.2, G.ε₂_mem_inf.1,
    G.z_ne_one, ⟨hzK₁, hzK₂⟩, ?_⟩⟩
  intro t ht
  rcases prod₁.split t ht.1 with h | h
  · exact Or.inl ⟨h, (hKT t ht).1 h⟩
  · exact Or.inr ⟨h, (hKT _ (Subgroup.mul_mem _ G.ε₁_mem_inf ht)).1 h⟩

end Assembly

end CFSG.Quasithin.F6.GoldAmS
