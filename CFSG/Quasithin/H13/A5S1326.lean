module

public import CFSG.Quasithin.H13.A5S132
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.Background.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Alt
public import CFSG.Quasithin.H13.A5S135

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.LieType.BorelTits
open CFSG.Blueprint

@[expose] def Stmt5_1_7_one : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsSylowTwo T →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L →
    (∃ n : ℕ, 2 ≤ n ∧ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 n) →
    quasithinIsMaxTwoLocal M → T ≤ M → L ≤ M → M ≤ Subgroup.normalizer (L : Set G) →
      Subgroup.normalizer (baum T : Set G) ≤ M

@[expose] def e01 : W5 := Multiplicative.ofAdd (e2 0 1)

@[expose] def e23 : W5 := Multiplicative.ofAdd (e2 2 3)

@[expose] def InV4 (σ : Equiv.Perm (Fin 5)) : Prop :=
  σ = 1 ∨ σ = Equiv.swap 0 1 ∨ σ = Equiv.swap 2 3 ∨ σ = pa

instance : DecidablePred InV4 := fun σ =>
  inferInstanceAs (Decidable (σ = 1 ∨ σ = Equiv.swap 0 1 ∨ σ = Equiv.swap 2 3 ∨ σ = pa))

theorem W2_nonsing : ∀ x : W5, InW2 x → x ≠ 1 → x ≠ W4 → x = e01 ∨ x = e23 := by
  decide +kernel

theorem e01_props : InW2 e01 ∧ e01 ≠ 1 ∧ e01 ≠ W4 ∧ ¬ IsSing e01 := by
  decide +kernel

theorem isSing_one_W4 : IsSing 1 ∧ W4 ≠ 1 := by
  decide +kernel

theorem D_inv_of_not_fixW2 : ∀ σ : Equiv.Perm (Fin 5), InD σ → σ * σ = 1 → ¬ FixW2 σ →
    σ = pb ∨ σ = pc := by
  decide +kernel

theorem InK4_of_comm_pb_pc : ∀ σ : Equiv.Perm (Fin 5), InD σ → σ * σ = 1 →
    (σ * pb = pb * σ ∨ σ * pc = pc * σ) → InK4 σ := by
  decide +kernel

theorem fix_K4_pair : ∀ σ ∈ [pa, pb, pc], ∀ τ ∈ [pa, pb, pc], σ ≠ τ → ∀ x : W5,
    pact σ x = x → pact τ x = x → x = 1 ∨ x = W4 := by
  decide +kernel

theorem card_one_W4 : Fintype.card {x : W5 // x = 1 ∨ x = W4} = 2 := by
  decide +kernel

theorem card_InK4 : Fintype.card {σ : Equiv.Perm (Fin 5) // InK4 σ} = 4 := by
  decide +kernel

theorem InV4_of_D_fix : ∀ σ : Equiv.Perm (Fin 5), InD σ → ∀ e ∈ [e01, e23], pact σ e = e →
    InV4 σ := by
  decide +kernel

theorem V4_props : ∀ σ : Equiv.Perm (Fin 5), InV4 σ →
    InD σ ∧ ∀ e ∈ [e01, e23], pact σ e = e := by
  decide +kernel

theorem K4_fix_e : ∀ σ : Equiv.Perm (Fin 5), InK4 σ → ∀ e ∈ [e01, e23], pact σ e = e →
    σ = 1 ∨ σ = pa := by
  decide +kernel

theorem InV4_of_normalizes : ∀ σ : Equiv.Perm (Fin 5), σ ^ 8 = 1 → ∀ e ∈ [e01, e23],
    pact σ e = e → (∀ τ ∈ [Equiv.swap 0 1, Equiv.swap 2 3, pa], InV4 (σ * τ * σ⁻¹)) →
      InV4 σ := by
  decide +kernel

theorem eq_of_even_normalizes : ∀ σ : Equiv.Perm (Fin 5), σ.sign = 1 → σ ^ 8 = 1 →
    ∀ e ∈ [e01, e23], pact σ e = e → σ * pa * σ⁻¹ = pa → σ = 1 ∨ σ = pa := by
  decide +kernel

theorem InK4_mul_inv_of_odd : ∀ σ : Equiv.Perm (Fin 5), InD σ → σ.sign ≠ 1 →
    ∀ τ : Equiv.Perm (Fin 5), InD τ → τ.sign ≠ 1 → InK4 (σ * τ⁻¹) := by
  decide +kernel

section General

variable {G : Type} [Group G]

theorem openPCore_eq_pCore' (p : ℕ) (X : Type*) [Group X] :
    CFSG.Open.pCore p X = CFSG.pCore p X := (CFSG.pCore_eq_open X p).symm

theorem map_conj_centralizer_singleton (a h : G) :
    (Subgroup.centralizer ({a} : Set G)).map (MulAut.conj h).toMonoidHom =
      Subgroup.centralizer ({h * a * h⁻¹} : Set G) := by
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hc' : c ∈ Subgroup.centralizer ({a} : Set G) := hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hc'
    show h * c * h⁻¹ ∈ Subgroup.centralizer ({h * a * h⁻¹} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc := hc'
    calc h * c * h⁻¹ * (h * a * h⁻¹) = h * (c * a) * h⁻¹ := by group
      _ = h * (a * c) * h⁻¹ := by rw [hc]
      _ = h * a * h⁻¹ * (h * c * h⁻¹) := by group
  · intro hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    refine ⟨h⁻¹ * x * h, ?_, ?_⟩
    · show h⁻¹ * x * h ∈ Subgroup.centralizer ({a} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc h⁻¹ * x * h * a = h⁻¹ * (x * (h * a * h⁻¹)) * h := by group
        _ = h⁻¹ * ((h * a * h⁻¹) * x) * h := by rw [hx]
        _ = a * (h⁻¹ * x * h) := by group
    · show h * (h⁻¹ * x * h) * h⁻¹ = x
      group

theorem card_map_conj (h : G) (H : Subgroup G) :
    Nat.card (H.map (MulAut.conj h).toMonoidHom) = Nat.card H :=
  Subgroup.card_map_of_injective (f := (MulAut.conj h).toMonoidHom) (MulAut.conj h).injective

variable [Finite G]

theorem card_eq_of_isSylowTwoOf {S S' H : Subgroup G} (hS : IsSylowTwoOf S H)
    (hS' : IsSylowTwoOf S' H) : Nat.card S = Nat.card S' := by
  obtain ⟨h, -, hconj⟩ := A4.exists_conj_of_isSylowTwoOf hS hS'
  have : S' = S.map (MulAut.conj h).toMonoidHom := by
    ext x
    rw [hconj x]
    constructor
    · intro hx
      exact ⟨h⁻¹ * x * h, hx, by show h * (h⁻¹ * x * h) * h⁻¹ = x; group⟩
    · rintro ⟨y, hy, rfl⟩
      have e : h⁻¹ * (h * y * h⁻¹) * h = y := by group
      show h⁻¹ * (h * y * h⁻¹) * h ∈ S
      rw [e]
      exact hy
  rw [this, card_map_conj]

theorem card_mul_le_of_isMaxElemAbelian {T V A : Subgroup G} (hV : IsElemAbelian 2 V)
    (hVT : V ≤ T) (hA : IsMaxElemAbelian T A) :
    Nat.card V * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) ≤
      Nat.card A * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := by
  have hK : IsElemAbelian 2 (A ⊓ Subgroup.centralizer (V : Set G)) :=
    B2F.isElemAbelian_mono inf_le_left hA.2.1
  have hcomm : ∀ k ∈ A ⊓ Subgroup.centralizer (V : Set G), ∀ v ∈ V, k * v = v * k :=
    fun k hk v hv => (Subgroup.mem_centralizer_iff.mp hk.2 v hv).symm
  have hD := B2F.isElemAbelian_sup_of_commute hK hV hcomm
  have hDT : (A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V ≤ T :=
    sup_le (inf_le_left.trans hA.1) hVT
  have hcard := B2F.card_sup_mul_card_inf_of_commute hcomm
  have hle := hA.2.2 _ hDT hD
  have hinf : Nat.card ↥((A ⊓ Subgroup.centralizer (V : Set G)) ⊓ V) ≤
      Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := by
    refine Subgroup.card_le_of_le fun x hx => ⟨hx.2, ?_⟩
    show x ∈ Subgroup.centralizer (A : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact B2F.isElemAbelian_comm hA.2.1 ha hx.1.1
  calc Nat.card V * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G))
      = Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) * Nat.card V := mul_comm _ _
    _ = Nat.card ↥((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V) *
          Nat.card ↥((A ⊓ Subgroup.centralizer (V : Set G)) ⊓ V) := hcard.symm
    _ ≤ Nat.card A * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) :=
      Nat.mul_le_mul hle hinf

omit [Finite G] in
theorem card_le_of_range_subset {A K : Subgroup G} {P : Type*} [Group P] [Finite P]
    (hKA : K ≤ A) (f : ↥A →* P) (hf : f.ker = K.subgroupOf A) (X : Set P)
    (hX : ∀ a, f a ∈ X) : Nat.card A ≤ Nat.card X * Nat.card K := by
  have h1 := Subgroup.card_mul_index (K.subgroupOf A)
  rw [← hf, Subgroup.index_ker] at h1
  have h2 : Nat.card ↥(K.subgroupOf A) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKA).toEquiv
  have h3 : Nat.card f.range ≤ Nat.card X := by
    have hsub : ((f.range : Subgroup P) : Set P) ⊆ X := by
      rintro _ ⟨a, rfl⟩
      exact hX a
    exact Nat.card_mono (Set.toFinite X) hsub
  rw [← hf] at h2
  rw [← h1, h2, mul_comm]
  exact Nat.mul_le_mul_right _ h3

end General

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem mem_centralizer_V2_iff (g : ↥(Subgroup.normalizer (V : Set G))) :
    (g : G) ∈ Subgroup.centralizer (S.V2 : Set G) ↔ FixW2 (S.frame.ρ g) := by
  constructor
  · intro hg x hx
    obtain ⟨v, rfl⟩ := S.frame.ψ.surjective x
    have hv : (v : G) ∈ S.V2 := S.mem_pre.2 ⟨v.2, by rw [Subtype.coe_eta]; exact mem_W2.2 hx⟩
    have hc := Subgroup.mem_centralizer_iff.mp hg v hv
    refine (S.conj_eq_iff g v).1 ?_
    calc (g : G) * v * (g : G)⁻¹ = v * g * (g : G)⁻¹ := by rw [hc]
      _ = v := by group
  · intro hfix
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    obtain ⟨hvV, hvW⟩ := S.mem_pre.1 hv
    have hc := (S.conj_eq_iff g ⟨v, hvV⟩).2 (hfix _ (mem_W2.1 hvW))
    calc v * g = (g : G) * v * (g : G)⁻¹ * g := by rw [hc]
      _ = g * v := by group

theorem rho_props_of_isMaxElemAbelian {A : Subgroup G} (hA : IsMaxElemAbelian T A) {b c : G}
    (hb : b ∈ A) (hc : c ∈ A) :
    InD (S.frame.ρ ⟨b, S.frame.T_le (hA.1 hb)⟩) ∧
      S.frame.ρ ⟨b, S.frame.T_le (hA.1 hb)⟩ * S.frame.ρ ⟨b, S.frame.T_le (hA.1 hb)⟩ = 1 ∧
      S.frame.ρ ⟨b, S.frame.T_le (hA.1 hb)⟩ * S.frame.ρ ⟨c, S.frame.T_le (hA.1 hc)⟩ =
        S.frame.ρ ⟨c, S.frame.T_le (hA.1 hc)⟩ * S.frame.ρ ⟨b, S.frame.T_le (hA.1 hb)⟩ := by
  refine ⟨S.frame.T_D _ (hA.1 hb), ?_, ?_⟩
  · rw [← map_mul]
    have : (⟨b, S.frame.T_le (hA.1 hb)⟩ : ↥(Subgroup.normalizer (V : Set G))) *
        ⟨b, S.frame.T_le (hA.1 hb)⟩ = 1 :=
      Subtype.ext (by simpa [pow_two] using hA.2.1.2 b hb)
    rw [this, map_one]
  · rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (B2F.isElemAbelian_comm hA.2.1 hb hc)

theorem ker_rho_restrict {A : Subgroup G} (hAN : A ≤ Subgroup.normalizer (V : Set G)) :
    (S.frame.ρ.comp (Subgroup.inclusion hAN)).ker =
      (A ⊓ Subgroup.centralizer (V : Set G)).subgroupOf A := by
  ext b
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.comp_apply]
  constructor
  · intro h
    exact ⟨b.2, S.frame.mem_centralizer_of_rho _ h⟩
  · intro h
    exact S.frame.rho_eq_one_of_mem _ h.2

theorem le_centralizer_V2_of_isMaxElemAbelian {A : Subgroup G} (hA : IsMaxElemAbelian T A) :
    A ≤ Subgroup.centralizer (S.V2 : Set G) := by
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hA.1.trans S.frame.T_le
  by_contra hA2
  obtain ⟨a, haA, ha⟩ := IsConcreteLE.not_le_iff_exists.1 hA2
  have hra : ¬ FixW2 (S.frame.ρ ⟨a, hAN haA⟩) := fun h =>
    ha ((S.mem_centralizer_V2_iff ⟨a, hAN haA⟩).2 h)
  have hpa := S.rho_props_of_isMaxElemAbelian hA haA haA
  have hpbc := D_inv_of_not_fixW2 _ hpa.1 hpa.2.1 hra
  have hK4 : ∀ b (hb : b ∈ A), InK4 (S.frame.ρ ⟨b, hAN hb⟩) := by
    intro b hb
    have hp := S.rho_props_of_isMaxElemAbelian hA hb haA
    refine InK4_of_comm_pb_pc _ hp.1 hp.2.1 ?_
    rcases hpbc with h | h
    · left; rw [← h]; exact hp.2.2
    · right; rw [← h]; exact hp.2.2
  have hff := card_mul_le_of_isMaxElemAbelian S.elemAbelian_V S.V_le_T hA
  rw [S.card_V] at hff
  have hKpos : 0 < Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := Nat.card_pos
  set f := S.frame.ρ.comp (Subgroup.inclusion hAN)
  have hfker := S.ker_rho_restrict hAN
  have hfval : ∀ b : ↥A, f b = S.frame.ρ ⟨(b : G), hAN b.2⟩ := fun _ => rfl
  by_cases hcase : ∃ (b : G) (hb : b ∈ A), S.frame.ρ ⟨b, hAN hb⟩ ≠ 1 ∧
      S.frame.ρ ⟨b, hAN hb⟩ ≠ S.frame.ρ ⟨a, hAN haA⟩
  ·
    obtain ⟨b, hbA, hb1, hba⟩ := hcase
    have hA4 := card_le_of_range_subset inf_le_left f hfker {σ | InK4 σ}
      fun c => by rw [hfval]; exact hK4 c c.2
    have hX4 : Nat.card ({σ | InK4 σ} : Set (Equiv.Perm (Fin 5))) = 4 := by
      rw [← card_InK4, ← Nat.card_eq_fintype_card]
      rfl
    rw [hX4] at hA4
    have hCV : Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) ≤ 2 := by
      rw [← card_one_W4, ← Nat.card_eq_fintype_card]
      refine Nat.card_le_card_of_injective
        (fun v => ⟨S.frame.ψ ⟨v, v.2.1⟩, ?_⟩) ?_
      · have hfa : pact (S.frame.ρ ⟨a, hAN haA⟩) (S.frame.ψ ⟨v, v.2.1⟩) =
            S.frame.ψ ⟨v, v.2.1⟩ := by
          refine (S.conj_eq_iff ⟨a, hAN haA⟩ ⟨v, v.2.1⟩).1 ?_
          have := Subgroup.mem_centralizer_iff.mp v.2.2 a haA
          show a * (v : G) * a⁻¹ = v
          rw [this]; group
        have hfb : pact (S.frame.ρ ⟨b, hAN hbA⟩) (S.frame.ψ ⟨v, v.2.1⟩) =
            S.frame.ψ ⟨v, v.2.1⟩ := by
          refine (S.conj_eq_iff ⟨b, hAN hbA⟩ ⟨v, v.2.1⟩).1 ?_
          have := Subgroup.mem_centralizer_iff.mp v.2.2 b hbA
          show b * (v : G) * b⁻¹ = v
          rw [this]; group
        have hmemA : S.frame.ρ ⟨a, hAN haA⟩ ∈ [pa, pb, pc] := by
          rcases hpbc with h | h <;> simp [h]
        have hmemB : S.frame.ρ ⟨b, hAN hbA⟩ ∈ [pa, pb, pc] := by
          rcases hK4 b hbA with h | h | h | h
          · exact absurd h hb1
          all_goals simp [h]
        exact fix_K4_pair _ hmemA _ hmemB (Ne.symm hba) _ hfa hfb
      · intro v w hvw
        have h1 := S.frame.ψ.injective (congrArg Subtype.val hvw)
        exact Subtype.ext (congrArg (fun x : ↥V => (x : G)) h1)
    have : 16 * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) ≤
        8 * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) :=
      calc 16 * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G))
          ≤ Nat.card A * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := hff
        _ ≤ (4 * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G))) * 2 :=
          Nat.mul_le_mul hA4 hCV
        _ = 8 * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := by ring
    omega
  ·
    push Not at hcase
    have hA2 := card_le_of_range_subset inf_le_left f hfker
      {σ | σ = 1 ∨ σ = S.frame.ρ ⟨a, hAN haA⟩} fun c => by
        rw [hfval]
        by_cases h1 : S.frame.ρ ⟨(c : G), hAN c.2⟩ = 1
        · exact Or.inl h1
        · exact Or.inr (hcase c c.2 h1)
    have hX2 : Nat.card ({σ | σ = 1 ∨ σ = S.frame.ρ ⟨a, hAN haA⟩} :
        Set (Equiv.Perm (Fin 5))) ≤ 2 := by
      have : ({σ | σ = 1 ∨ σ = S.frame.ρ ⟨a, hAN haA⟩} : Set (Equiv.Perm (Fin 5))) =
          {1, S.frame.ρ ⟨a, hAN haA⟩} := by
        ext σ; simp
      rw [this, Nat.card_coe_set_eq]
      exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
    have hra1 : S.frame.ρ ⟨a, hAN haA⟩ ≠ 1 := by
      rcases hpbc with h | h <;> rw [h] <;> decide
    have hCV : Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) ≤ 4 := by
      rw [← card_fix_K4 _ (hK4 a haA) hra1, ← Nat.card_eq_fintype_card]
      refine Nat.card_le_card_of_injective (fun v => ⟨S.frame.ψ ⟨v, v.2.1⟩, ?_⟩) ?_
      · refine (S.conj_eq_iff ⟨a, hAN haA⟩ ⟨v, v.2.1⟩).1 ?_
        have := Subgroup.mem_centralizer_iff.mp v.2.2 a haA
        show a * (v : G) * a⁻¹ = v
        rw [this]; group
      · intro v w hvw
        have h1 := S.frame.ψ.injective (congrArg Subtype.val hvw)
        exact Subtype.ext (congrArg (fun x : ↥V => (x : G)) h1)
    have : 16 * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) ≤
        8 * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) :=
      calc 16 * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G))
          ≤ Nat.card A * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := hff
        _ ≤ (2 * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G))) * 4 :=
          Nat.mul_le_mul (hA2.trans (Nat.mul_le_mul_right _ hX2)) hCV
        _ = 8 * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := by ring
    omega

theorem thompsonJ_le_centralizer_V2 : thompsonJ T ≤ Subgroup.centralizer (S.V2 : Set G) :=
  iSup₂_le fun _ hA => S.le_centralizer_V2_of_isMaxElemAbelian hA

theorem V2_le_omegaOneCenter_J : S.V2 ≤ omegaOneCenterOf (thompsonJ T) := by
  intro v hv
  have hvV : v ∈ V := S.pre_le_V _ hv
  have hv2 : v ^ 2 = 1 := S.elemAbelian_V.2 v hvV
  have hvA : ∀ A, IsMaxElemAbelian T A → v ∈ A := by
    intro A hA
    refine (eq_omegaOneOf_centralizer hA).ge (Subgroup.subset_closure ⟨⟨S.V_le_T hvV, ?_⟩, hv2⟩)
    show v ∈ Subgroup.centralizer (A : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp (S.le_centralizer_V2_of_isMaxElemAbelian hA ha)
      v hv).symm
  obtain ⟨A, hA⟩ := exists_isMaxElemAbelian T
  refine Subgroup.subset_closure ⟨⟨?_, ?_⟩, hv2⟩
  · exact (le_iSup₂_of_le A hA le_rfl : A ≤ thompsonJ T) (hvA A hA)
  · show v ∈ Subgroup.centralizer (thompsonJ T : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact (Subgroup.mem_centralizer_iff.mp (S.thompsonJ_le_centralizer_V2 hj) v hv).symm

theorem baum_le_centralizer_V2 : baum T ≤ Subgroup.centralizer (S.V2 : Set G) :=
  inf_le_right.trans (Subgroup.centralizer_le S.V2_le_omegaOneCenter_J)

theorem lieModel_L : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 2 := by
  obtain ⟨φ, hφ, hker⟩ := S.a5
  have hk : φ.ker = CFSG.pCore 2 ↥L := hker.trans (openPCore_eq_pCore' 2 ↥L)
  exact Or.inl ⟨by decide,
    CFSG.QuasithinUnique.Ch1.statedClassicalModel_psl_two_four_of_alternating_five
      _ ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩⟩

theorem normalizer_baum_le (h517 : Stmt5_1_7_one) :
    Subgroup.normalizer (baum T : Set G) ≤ Subgroup.normalizer (L : Set G) :=
  h517 G T L _ S.h13.simple S.h13.nonabelian S.h13.qtke S.h13.sylow S.maximal S.h13.faithful
    ⟨2, le_rfl, S.lieModel_L⟩ S.uniqueM.1.1 S.T_le_NL Subgroup.le_normalizer le_rfl

theorem exists_T_of_D (hodd : ∃ (t : G) (ht : t ∈ T), (S.frame.ρ ⟨t, S.frame.T_le ht⟩).sign ≠ 1)
    {σ : Equiv.Perm (Fin 5)} (hσ : InD σ) :
    ∃ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ T ∧ S.frame.ρ g = σ := by
  by_cases hs : σ.sign = 1
  · exact S.frame.K4_T σ (InK4_of_D_alt σ hσ hs)
  · obtain ⟨t₀, ht₀, hodd₀⟩ := hodd
    obtain ⟨g₁, hg₁T, hg₁⟩ := S.frame.K4_T _
      (InK4_mul_inv_of_odd σ hσ hs _ (S.frame.T_D _ ht₀) hodd₀)
    refine ⟨g₁ * ⟨t₀, S.frame.T_le ht₀⟩, T.mul_mem hg₁T ht₀, ?_⟩
    rw [map_mul, hg₁]
    group

theorem isSylowTwoOf_centralizer
    (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one) {v : G}
    (hv : v ∈ S.V2) (hv1 : v ∉ S.V1) :
    IsSylowTwoOf (T ⊓ Subgroup.centralizer ({v} : Set G))
      (Subgroup.centralizer ({v} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hvV : v ∈ V := S.pre_le_V _ hv
  have hψW2 : InW2 (S.frame.ψ ⟨v, hvV⟩) := by
    obtain ⟨h, hW⟩ := S.mem_pre.1 hv
    exact mem_W2.1 hW
  have hψ1 : S.frame.ψ ⟨v, hvV⟩ ≠ 1 := by
    intro h
    apply hv1
    rw [S.mem_V1]
    left
    have : (⟨v, hvV⟩ : ↥V) = 1 := S.frame.ψ.injective (by rw [h, map_one])
    exact congrArg Subtype.val this
  have hψ4 : S.frame.ψ ⟨v, hvV⟩ ≠ W4 := by
    intro h
    apply hv1
    rw [S.mem_V1]
    right
    have : (⟨v, hvV⟩ : ↥V) = ⟨S.z, S.z_mem_V⟩ := S.frame.ψ.injective (by rw [h, S.psi_z])
    exact congrArg Subtype.val this
  have he : S.frame.ψ ⟨v, hvV⟩ ∈ [e01, e23] := by
    rcases W2_nonsing _ hψW2 hψ1 hψ4 with h | h <;> simp [h]
  have hmemTv : ∀ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ T →
      pact (S.frame.ρ g) (S.frame.ψ ⟨v, hvV⟩) = S.frame.ψ ⟨v, hvV⟩ →
        (g : G) ∈ T ⊓ Subgroup.centralizer ({v} : Set G) := by
    intro g hgT hfix
    refine ⟨hgT, ?_⟩
    show (g : G) ∈ Subgroup.centralizer ({v} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := (S.conj_eq_iff g ⟨v, hvV⟩).2 hfix
    calc (g : G) * v = (g : G) * v * (g : G)⁻¹ * g := by group
      _ = v * g := by rw [this]
  have hfixTv : ∀ g : ↥(Subgroup.normalizer (V : Set G)),
      (g : G) ∈ T ⊓ Subgroup.centralizer ({v} : Set G) →
        pact (S.frame.ρ g) (S.frame.ψ ⟨v, hvV⟩) = S.frame.ψ ⟨v, hvV⟩ := by
    intro g hg
    refine (S.conj_eq_iff g ⟨v, hvV⟩).1 ?_
    have := Subgroup.mem_centralizer_singleton_iff.mp hg.2
    show (g : G) * v * (g : G)⁻¹ = v
    rw [this]; group
  have hBTv : baum T ≤ T ⊓ Subgroup.centralizer ({v} : Set G) := by
    refine le_inf inf_le_left fun x hx => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (S.baum_le_centralizer_V2 hx) v hv).symm
  have hBeq : baum T = baum (T ⊓ Subgroup.centralizer ({v} : Set G)) :=
    baum_eq_of_le hBTv inf_le_left
  obtain ⟨P, hP, hTvP⟩ := A4.exists_isSylowTwoOf_ge
    (inf_le_right : T ⊓ Subgroup.centralizer ({v} : Set G) ≤ Subgroup.centralizer ({v} : Set G))
    (S.isPGroup_T.to_le inf_le_left)
  suffices hPT : P ≤ T ⊓ Subgroup.centralizer ({v} : Set G) by
    rw [le_antisymm hTvP hPT]
    exact hP
  by_contra hPT
  obtain ⟨x, hxP, hxTv, hxN⟩ :=
    exists_mem_normalizer_not_mem hP.2.1 (lt_of_le_of_ne hTvP fun h => hPT h.ge)
  have hxB : x ∈ Subgroup.normalizer (baum T : Set G) := by
    rw [hBeq]
    exact normalizer_le_normalizer_baum _ hxN
  have hxM := S.normalizer_baum_le h517 hxB
  have hxC : x ∈ Subgroup.centralizer ({v} : Set G) := hP.1 hxP
  have hv1' : v ≠ 1 := fun h => hv1 (h ▸ Subgroup.one_mem _)
  have hxU : x ∈ Subgroup.normalizer (Subgroup.zpowers v : Set G) := by
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hc : Commute v x := (Subgroup.mem_centralizer_singleton_iff.mp hxC).symm
    exact (hc.zpow_left k).eq
  have hxV : x ∈ Subgroup.normalizer (V : Set G) := S.mem_normalizer_V_of h1222 hxM
    (Subgroup.zpowers_ne_bot.mpr hv1') (Subgroup.zpowers_le.mpr hvV) hxU
  have hRTv : pCoreOf 2 (L ⊔ T) ≤ T ⊓ Subgroup.centralizer ({v} : Set G) := by
    refine le_inf S.pCoreOf_LT_le_T fun r hr => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (S.R_sylow_CV.1 hr) v hvV).symm
  have hPCV : P ⊓ Subgroup.centralizer (V : Set G) ≤ T ⊓ Subgroup.centralizer ({v} : Set G) := by
    refine le_trans ?_ hRTv
    exact (A4.isSylowTwoOf_iff_maximal.mp S.R_sylow_CV).2.2 _ inf_le_right
      (hP.2.1.to_le inf_le_left) (le_inf (hRTv.trans hTvP) S.R_sylow_CV.1)
  set σ := S.frame.ρ ⟨x, hxV⟩ with hσdef
  have hσ8 : σ ^ 8 = 1 := by
    obtain ⟨k, hk⟩ := hP.2.1 ⟨x, hxP⟩
    refine pow_eight_of_pow_two_pow (k := k) ?_
    rw [hσdef, ← map_pow]
    have : (⟨x, hxV⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  have hσe : pact σ (S.frame.ψ ⟨v, hvV⟩) = S.frame.ψ ⟨v, hvV⟩ := by
    refine (S.conj_eq_iff ⟨x, hxV⟩ ⟨v, hvV⟩).1 ?_
    have := Subgroup.mem_centralizer_singleton_iff.mp hxC
    show x * v * x⁻¹ = v
    rw [this]; group
  have hconj : ∀ g : ↥(Subgroup.normalizer (V : Set G)),
      (g : G) ∈ T ⊓ Subgroup.centralizer ({v} : Set G) →
        ∃ g' : ↥(Subgroup.normalizer (V : Set G)),
          (g' : G) ∈ T ⊓ Subgroup.centralizer ({v} : Set G) ∧
            S.frame.ρ g' = σ * S.frame.ρ g * σ⁻¹ := by
    intro g hg
    refine ⟨⟨x, hxV⟩ * g * ⟨x, hxV⟩⁻¹, ?_, by rw [map_mul, map_mul, map_inv, ← hσdef]⟩
    exact (Subgroup.mem_normalizer_iff.mp hxN g).mp hg
  have key : ∃ g : ↥(Subgroup.normalizer (V : Set G)),
      (g : G) ∈ T ⊓ Subgroup.centralizer ({v} : Set G) ∧ S.frame.ρ g = σ := by
    by_cases hodd : ∃ (t : G) (ht : t ∈ T), (S.frame.ρ ⟨t, S.frame.T_le ht⟩).sign ≠ 1
    ·
      have hV4 : ∀ τ, InV4 τ → ∃ g : ↥(Subgroup.normalizer (V : Set G)),
          (g : G) ∈ T ⊓ Subgroup.centralizer ({v} : Set G) ∧ S.frame.ρ g = τ := by
        intro τ hτ
        obtain ⟨g, hgT, hgτ⟩ := S.exists_T_of_D hodd (V4_props τ hτ).1
        refine ⟨g, hmemTv g hgT ?_, hgτ⟩
        rw [hgτ]
        exact (V4_props τ hτ).2 _ he
      have hσV4 : InV4 σ := by
        refine InV4_of_normalizes σ hσ8 _ he hσe fun τ hτ => ?_
        have hτV4 : InV4 τ := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hτ
          rcases hτ with rfl | rfl | rfl <;> decide
        obtain ⟨g, hg, rfl⟩ := hV4 τ hτV4
        obtain ⟨g', hg', hg'ρ⟩ := hconj g hg
        rw [← hg'ρ]
        exact InV4_of_D_fix _ (S.frame.T_D g' hg'.1) _ he (hfixTv g' hg')
      exact hV4 σ hσV4
    ·
      push Not at hodd
      have hσsign : σ.sign = 1 := by
        by_contra hne
        have hT : IsSylowTwoOf T (Subgroup.normalizer (V : Set G)) :=
          isSylowTwoOf_of_le S.h13.sylow S.frame.T_le
        set f : ↥(Subgroup.normalizer (V : Set G)) →* ℤˣ := Equiv.Perm.sign.comp S.frame.ρ
        have hsurj : Function.Surjective f := by
          intro u
          rcases Int.units_eq_one_or u with rfl | rfl
          · exact ⟨1, map_one f⟩
          · refine ⟨⟨x, hxV⟩, ?_⟩
            show Equiv.Perm.sign σ = -1
            rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
            · exact absurd h hne
            · exact h
        have hidx : f.ker.index = 2 := by
          rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top,
            Nat.card_eq_fintype_card, Fintype.card_units_int]
        have hle : T.subgroupOf (Subgroup.normalizer (V : Set G)) ≤ f.ker := by
          intro t ht
          rw [MonoidHom.mem_ker]
          exact hodd t ht
        have := Subgroup.index_dvd_of_le hle
        rw [hidx] at this
        exact hT.2.2 this
      obtain ⟨gpa, hgpaT, hgpa⟩ := S.frame.K4_T pa (by decide)
      have hpaTv : (gpa : G) ∈ T ⊓ Subgroup.centralizer ({v} : Set G) := by
        refine hmemTv gpa hgpaT ?_
        rw [hgpa]
        exact (V4_props pa (by decide)).2 _ he
      have hσpa : σ * pa * σ⁻¹ = pa := by
        obtain ⟨g', hg', hg'ρ⟩ := hconj gpa hpaTv
        rw [hgpa] at hg'ρ
        have hK : InK4 (S.frame.ρ g') :=
          InK4_of_D_alt _ (S.frame.T_D g' hg'.1) (hodd _ hg'.1)
        rcases K4_fix_e _ hK _ he (hfixTv g' hg') with h | h
        · rw [h] at hg'ρ
          exfalso
          have : pa = 1 :=
            calc pa = σ⁻¹ * (σ * pa * σ⁻¹) * σ := by group
              _ = σ⁻¹ * 1 * σ := by rw [← hg'ρ]
              _ = 1 := by group
          exact absurd this (by decide)
        · rw [← hg'ρ, h]
      rcases eq_of_even_normalizes σ hσsign hσ8 _ he hσe hσpa with h | h
      · exact ⟨1, Subgroup.one_mem _, by rw [map_one, h]⟩
      · exact ⟨gpa, hpaTv, by rw [hgpa, h]⟩
  obtain ⟨g, hgTv, hgσ⟩ := key
  have hxg : x * (g : G)⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
    have := S.frame.mem_centralizer_of_rho (⟨x, hxV⟩ * g⁻¹) (by rw [map_mul, map_inv, hgσ,
      ← hσdef, mul_inv_cancel])
    simpa using this
  have hxgP : x * (g : G)⁻¹ ∈ P := P.mul_mem hxP (P.inv_mem (hTvP hgTv))
  have := hPCV ⟨hxgP, hxg⟩
  apply hxTv
  have := (T ⊓ Subgroup.centralizer ({v} : Set G)).mul_mem this hgTv
  simpa using this

theorem isSing_of_conj
    (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one) {g : G} {v w : ↥V}
    (hgvw : g * v * g⁻¹ = w) (hv : IsSing (S.frame.ψ v)) : IsSing (S.frame.ψ w) := by
  by_contra hw
  have hw1 : S.frame.ψ w ≠ 1 := fun h => hw (h ▸ isSing_one_W4.1)
  have hv1 : S.frame.ψ v ≠ 1 := by
    intro h
    apply hw1
    have hv1 : v = 1 := S.frame.ψ.injective (by rw [h, map_one])
    have : w = 1 := by
      apply Subtype.ext
      rw [← hgvw, hv1]
      simp
    rw [this, map_one]
  obtain ⟨σ, hσ, hσv⟩ := exists_alt_pact _ _ hv1 isSing_one_W4.2 (iff_of_true hv isSing_W4)
  obtain ⟨l, hlL, hlσ⟩ := (S.frame.image_L σ).2 hσ
  obtain ⟨σ', hσ', hσ'w⟩ := exists_alt_pact _ _ hw1 e01_props.2.1 (iff_of_false hw e01_props.2.2.2)
  obtain ⟨l', hl'L, hl'σ'⟩ := (S.frame.image_L σ').2 hσ'
  have hz : (l : G) * v * (l : G)⁻¹ = S.z := by
    have := S.psi_conj l v
    rw [hlσ, hσv, ← S.psi_z] at this
    exact congrArg Subtype.val (S.frame.ψ.injective this)
  have hw'V : (l' : G) * w * (l' : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp l'.2 w).mp w.2
  have hψw' : S.frame.ψ ⟨(l' : G) * w * (l' : G)⁻¹, hw'V⟩ = e01 := by
    rw [S.psi_conj l' w, hl'σ', hσ'w]
  have hhz : ((l' : G) * g * (l : G)⁻¹) * S.z * ((l' : G) * g * (l : G)⁻¹)⁻¹ =
      (l' : G) * w * (l' : G)⁻¹ := by
    rw [← hz, ← hgvw]
    group
  have hw'2 : (l' : G) * w * (l' : G)⁻¹ ∈ S.V2 :=
    S.mem_pre.2 ⟨hw'V, by rw [hψw']; exact mem_W2.2 e01_props.1⟩
  have hw'1 : (l' : G) * w * (l' : G)⁻¹ ∉ S.V1 := by
    intro h
    rcases S.mem_V1.1 h with h1 | h1
    · have : (⟨_, hw'V⟩ : ↥V) = 1 := Subtype.ext h1
      rw [this, map_one] at hψw'
      exact e01_props.2.1 hψw'.symm
    · have : (⟨_, hw'V⟩ : ↥V) = ⟨S.z, S.z_mem_V⟩ := Subtype.ext h1
      rw [this, S.psi_z] at hψw'
      exact e01_props.2.2.1 hψw'.symm
  have hS1 := S.isSylowTwoOf_centralizer h1222 h517 hw'2 hw'1
  have hTz : T ≤ Subgroup.centralizer ({S.z} : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := S.conj_z_of_mem_T ht
    calc t * S.z = t * S.z * t⁻¹ * t := by group
      _ = S.z * t := by rw [this]
  have hS2 := isSylowTwoOf_map_conj (isSylowTwoOf_of_le S.h13.sylow hTz)
    ((l' : G) * g * (l : G)⁻¹)
  rw [map_conj_centralizer_singleton, hhz] at hS2
  have hcard := card_eq_of_isSylowTwoOf hS1 hS2
  rw [card_map_conj] at hcard
  have hTeq : T ⊓ Subgroup.centralizer ({(l' : G) * w * (l' : G)⁻¹} : Set G) = T :=
    Subgroup.eq_of_le_of_card_ge inf_le_left hcard.ge
  apply hw'1
  refine S.mem_V1_of_fixed hw'V fun t ht => ?_
  have ht' : t ∈ Subgroup.centralizer ({(l' : G) * w * (l' : G)⁻¹} : Set G) :=
    (hTeq.ge ht).2
  rw [Subgroup.mem_centralizer_singleton_iff] at ht'
  rw [ht']
  group

end Setting

theorem input1326Two_of
    (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one) : Input1326Two := by
  intro G _ _ T L V S g v w hgvw
  refine ⟨S.isSing_of_conj h1222 h517 hgvw, fun hw => ?_⟩
  refine S.isSing_of_conj h1222 h517 (g := g⁻¹) (v := w) (w := v) ?_ hw
  rw [← hgvw]
  group

end CFSG.Quasithin.H13.A5
