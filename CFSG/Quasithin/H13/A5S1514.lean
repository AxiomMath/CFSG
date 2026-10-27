module

public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.G2A5Two
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.H13.A5F91
public import CFSG.Quasithin.H13.A5Producer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def c3q : Equiv.Perm (Fin 5) := Equiv.swap 1 3 * Equiv.swap 1 2

theorem c3q_props : c3q.sign = 1 ∧ c3q 4 = 4 ∧ c3q ^ 3 = 1 := by decide

theorem c3p_props : c3p.sign = 1 ∧ c3p 4 = 4 ∧ c3p ^ 3 = 1 := ⟨c3p_sign, c3p_four, c3p_cube⟩

theorem pow_four_pow_of_cube {σ : Equiv.Perm (Fin 5)} (h3 : σ ^ 3 = 1) (a : ℕ) :
    σ ^ (4 ^ a) = σ := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ, pow_mul, ih, show σ ^ 4 = σ ^ 3 * σ from pow_succ σ 3, h3, one_mul]

@[expose] def CommDecomp2 (x y : W5) : Prop :=
  ∃ y' : W5, c4 y' = 1 ∧ x = y * (pact c3p y)⁻¹ * (y' * (pact c3q y')⁻¹)

instance (x y : W5) : Decidable (CommDecomp2 x y) :=
  inferInstanceAs (Decidable (∃ y' : W5, c4 y' = 1 ∧ x = y * (pact c3p y)⁻¹ *
    (y' * (pact c3q y')⁻¹)))

@[expose] def CommDecomp (x : W5) : Prop := ∃ y : W5, c4 y = 1 ∧ CommDecomp2 x y

instance (x : W5) : Decidable (CommDecomp x) :=
  inferInstanceAs (Decidable (∃ y : W5, c4 y = 1 ∧ CommDecomp2 x y))

theorem commDecomp_of_W3 : ∀ x : W5, c4 x = 1 → CommDecomp x := by
  decide +kernel

theorem W3_comm : ∀ x : W5, c4 x = 1 → ∃ y : W5, c4 y = 1 ∧ ∃ y' : W5, c4 y' = 1 ∧
    x = y * (pact c3p y)⁻¹ * (y' * (pact c3q y')⁻¹) :=
  commDecomp_of_W3

theorem comm_mem_W3 : ∀ (σ : Equiv.Perm (Fin 5)) (x : W5), σ 4 = 4 →
    c4 (x * (pact σ x)⁻¹) = 1 := by
  decide +kernel

theorem fix_alt_eq_one : ∀ x : W5,
    (∀ σ : Equiv.Perm (Fin 5), σ.sign = 1 → pact σ x = x) → x = 1 := by
  decide +kernel

theorem InK4_of_conj_D : ∀ σ : Equiv.Perm (Fin 5), InD σ → InD (c3p * σ * c3p⁻¹) →
    InD (c3p⁻¹ * σ * c3p) → InD (c3q * σ * c3q⁻¹) → InK4 σ := by
  decide +kernel

theorem K4_orbit : ∀ σ ∈ [pa, pb, pc], ∀ τ ∈ [pa, pb, pc],
    τ = σ ∨ τ = c3p * σ * c3p⁻¹ ∨ τ = c3p⁻¹ * σ * c3p := by
  decide +kernel

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem exists_L1_of_three {σ : Equiv.Perm (Fin 5)} (hs : σ.sign = 1) (h4 : σ 4 = 4)
    (h3 : σ ^ 3 = 1) : ∃ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ S.L1 ∧
      S.frame.ρ g = σ := by
  obtain ⟨g, hgL, hg⟩ := (S.frame.image_L σ).2 hs
  have hgz : (g : G) * S.z * (g : G)⁻¹ = S.z := by
    rw [S.conj_eq_iff g ⟨S.z, S.z_mem_V⟩, S.psi_z, hg]
    exact pact_W4 h4
  have hgN : (g : G) ∈ L ⊓ Subgroup.normalizer (S.V1 : Set G) := by
    refine ⟨hgL, ?_⟩
    show (g : G) ∈ Subgroup.normalizer (S.V1 : Set G)
    rw [S.normalizer_V1, Subgroup.mem_centralizer_singleton_iff]
    calc (g : G) * S.z = (g : G) * S.z * (g : G)⁻¹ * g := by group
      _ = S.z * g := by rw [hgz]
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  refine ⟨g ^ (4 ^ a), ?_, by rw [map_pow, hg, pow_four_pow_of_cube h3]⟩
  refine Subgroup.subset_closure ⟨?_, m, hm, ?_⟩
  · simpa using Subgroup.pow_mem _ hgN (4 ^ a)
  · have h1 : (g ^ (4 ^ a)) ^ m = (g ^ (2 ^ a * m)) ^ (2 ^ a) := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
      ring
    have h2 : g ^ (2 ^ a * m) = 1 := by rw [← hnm, pow_orderOf_eq_one]
    have h3 : (g ^ (4 ^ a)) ^ m = 1 := by rw [h1, h2, one_pow]
    simpa using congrArg Subtype.val h3

theorem psi_commutator (v : ↥V) (g : ↥(Subgroup.normalizer (V : Set G))) :
    ∃ h : ⁅(v : G), (g : G)⁆ ∈ V,
      S.frame.ψ ⟨⁅(v : G), (g : G)⁆, h⟩ = S.frame.ψ v * (pact (S.frame.ρ g) (S.frame.ψ v))⁻¹ := by
  have hc : (g : G) * (v : G)⁻¹ * (g : G)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp g.2 _).mp (V.inv_mem v.2)
  have he : ⁅(v : G), (g : G)⁆ = (v : G) * ((g : G) * (v : G)⁻¹ * (g : G)⁻¹) := by
    rw [commutatorElement_def]
    group
  refine ⟨he ▸ V.mul_mem v.2 hc, ?_⟩
  have h1 : (⟨⁅(v : G), (g : G)⁆, he ▸ V.mul_mem v.2 hc⟩ : ↥V) =
      v * ⟨(g : G) * (v⁻¹ : ↥V) * (g : G)⁻¹, by simpa using hc⟩ := Subtype.ext (by simpa using he)
  rw [h1, map_mul, S.psi_conj g v⁻¹]
  simp only [map_inv]

theorem commutator_V_L1_le : ⁅V, S.L1⁆ ≤ S.V3 := by
  rw [Subgroup.commutator_le]
  intro v hv l hl
  have hlN : l ∈ Subgroup.normalizer (V : Set G) :=
    S.frame.L_le (S.L1_le_L hl)
  obtain ⟨h, hψ⟩ := S.psi_commutator ⟨v, hv⟩ ⟨l, hlN⟩
  refine S.mem_pre.2 ⟨h, ?_⟩
  rw [hψ]
  refine mem_W3.2 (comm_mem_W3 _ _ ?_)
  exact S.rho_four_of_conj_z hlN (S.conj_z_of_normalizes (S.L1_le_NV1 hl))

theorem V3_le_commutator_V3_L1 : S.V3 ≤ ⁅S.V3, S.L1⁆ := by
  intro x hx
  obtain ⟨hxV, hx3⟩ := S.mem_pre.1 hx
  obtain ⟨y, hy, y', hy', he⟩ := W3_comm _ (mem_W3.1 hx3)
  obtain ⟨g, hgL1, hg⟩ := S.exists_L1_of_three c3p_props.1 c3p_props.2.1 c3p_props.2.2
  obtain ⟨g', hg'L1, hg'⟩ := S.exists_L1_of_three c3q_props.1 c3q_props.2.1 c3q_props.2.2
  obtain ⟨v, rfl⟩ := S.frame.ψ.surjective y
  obtain ⟨v', rfl⟩ := S.frame.ψ.surjective y'
  have hv3 : (v : G) ∈ S.V3 := S.mem_pre.2 ⟨v.2, by rw [Subtype.coe_eta]; exact mem_W3.2 hy⟩
  have hv'3 : (v' : G) ∈ S.V3 := S.mem_pre.2 ⟨v'.2, by rw [Subtype.coe_eta]; exact mem_W3.2 hy'⟩
  obtain ⟨h1, hψ1⟩ := S.psi_commutator v g
  obtain ⟨h2, hψ2⟩ := S.psi_commutator v' g'
  have hx_eq : x = ⁅(v : G), (g : G)⁆ * ⁅(v' : G), (g' : G)⁆ := by
    have : (⟨x, hxV⟩ : ↥V) = ⟨⁅(v : G), (g : G)⁆, h1⟩ * ⟨⁅(v' : G), (g' : G)⁆, h2⟩ := by
      apply S.frame.ψ.injective
      rw [map_mul, hψ1, hψ2, hg, hg']
      exact he
    exact congrArg Subtype.val this
  rw [hx_eq]
  exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator hv3 hgL1)
    (Subgroup.commutator_mem_commutator hv'3 hg'L1)

theorem commutator_V_L1 : ⁅V, S.L1⁆ = S.V3 :=
  le_antisymm S.commutator_V_L1_le
    (S.V3_le_commutator_V3_L1.trans (Subgroup.commutator_mono S.V3_le_V le_rfl))

theorem commutator_V3_L1 : ⁅S.V3, S.L1⁆ = S.V3 :=
  le_antisymm ((Subgroup.commutator_mono S.V3_le_V le_rfl).trans S.commutator_V_L1_le)
    S.V3_le_commutator_V3_L1

theorem V_inf_centralizer_L : V ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨hvV, hvC⟩
  have hfix : ∀ σ : Equiv.Perm (Fin 5), σ.sign = 1 →
      pact σ (S.frame.ψ ⟨v, hvV⟩) = S.frame.ψ ⟨v, hvV⟩ := by
    intro σ hσ
    obtain ⟨g, hgL, rfl⟩ := (S.frame.image_L σ).2 hσ
    refine (S.conj_eq_iff g ⟨v, hvV⟩).1 ?_
    have := Subgroup.mem_centralizer_iff.mp hvC g hgL
    show (g : G) * v * (g : G)⁻¹ = v
    rw [this]
    group
  have h1 := fix_alt_eq_one _ hfix
  have : (⟨v, hvV⟩ : ↥V) = 1 := S.frame.ψ.injective (by rw [h1, map_one])
  exact (Subgroup.mem_bot).2 (congrArg Subtype.val this)

theorem conjClosure_V1_L : conjClosure S.V1 L = V := by
  have hle : conjClosure S.V1 L ≤ V :=
    conjClosure_le fun l hl v hv =>
      (Subgroup.mem_normalizer_iff.mp (S.frame.L_le hl) v).mp (S.V1_le_V hv)
  rcases S.irr.2.2.2.2.2.1 (conjClosure S.V1 L) (by rw [S.V_inf_centralizer_L]; exact bot_le)
      hle (le_normalizer_conjClosure _ _) with h | h
  · exfalso
    rw [S.V_inf_centralizer_L] at h
    apply S.z_ne_one
    have : S.z ∈ conjClosure S.V1 L := le_conjClosure _ _ (S.mem_V1.2 (Or.inr rfl))
    rw [h] at this
    exact (Subgroup.mem_bot).1 this
  · exact h

theorem rho_L_mem_alt (l : ↥L) :
    S.frame.ρ ⟨l, S.frame.L_le l.2⟩ ∈ alternatingGroup (Fin 5) :=
  Equiv.Perm.mem_alternatingGroup.2 ((S.frame.image_L _).1 ⟨_, l.2, rfl⟩)

noncomputable def rawData5 : RawData5 L (pCoreOf 2 (L ⊔ T)) V where
  hnorm := S.frame.L_le
  θ := (S.frame.ρ.comp (Subgroup.inclusion S.frame.L_le)).codRestrict (alternatingGroup (Fin 5))
    fun l => S.rho_L_mem_alt l
  ψ := S.frame.ψ
  surj := by
    rintro ⟨σ, hσ⟩
    obtain ⟨g, hgL, hg⟩ := (S.frame.image_L σ).2 (Equiv.Perm.mem_alternatingGroup.1 hσ)
    exact ⟨⟨g, hgL⟩, Subtype.ext hg⟩
  ker_eq := by
    ext l
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : S.frame.ρ ⟨l, S.frame.L_le l.2⟩ = 1 := congrArg Subtype.val h
      have hC := S.frame.mem_centralizer_of_rho _ h1
      rw [← S.cLT]
      exact ⟨le_sup_left (a := L) l.2, hC⟩
    · intro h
      apply Subtype.ext
      have hC : (l : G) ∈ Subgroup.centralizer (V : Set G) := by
        rw [← S.cLT] at h
        exact h.2
      exact S.frame.rho_eq_one_of_mem ⟨l, S.frame.L_le l.2⟩ hC
  equiv := fun l v => S.frame.equiv ⟨l, S.frame.L_le l.2⟩ v

theorem isA5ModuleFor : IsA5ModuleFor L (pCoreOf 2 (L ⊔ T)) (conjClosure S.V1 L) := by
  rw [S.conjClosure_V1_L]
  exact ⟨S.rawData5⟩

theorem elemAbelian_of_le_centralizer {H : Subgroup G}
    (hU : conjClosure S.V3 H ≤ Subgroup.centralizer (V : Set G)) :
    IsElemAbelian 2 (conjClosure S.V3 H) := by
  refine B2F.isElemAbelian_closure ?_ ?_
  · rintro _ ⟨h, hh, x, hx, rfl⟩ _ ⟨k, hk, y, hy, rfl⟩
    have hky : k * y * k⁻¹ ∈ conjClosure S.V3 H := mem_conjClosure hk hy
    have hky' : h⁻¹ * (k * y * k⁻¹) * h ∈ conjClosure S.V3 H := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 H (H.inv_mem hh))
        (k * y * k⁻¹)).mp hky
      simpa [mul_assoc] using this
    have hc := Subgroup.mem_centralizer_iff.mp (hU hky') x (S.V3_le_V hx)
    calc h * x * h⁻¹ * (k * y * k⁻¹) = h * (x * (h⁻¹ * (k * y * k⁻¹) * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * (k * y * k⁻¹) * h) * x) * h⁻¹ := by rw [hc]
      _ = k * y * k⁻¹ * (h * x * h⁻¹) := by group
  · rintro _ ⟨h, -, x, hx, rfl⟩
    rw [conj_pow, S.elemAbelian_V.2 x (S.V3_le_V hx)]
    group

theorem conjClosure_V3_le_T (h1323 : Input1323Two) {H : Subgroup G} (hH : H ∈ S.Hz) :
    conjClosure S.V3 H ≤ T :=
  (S.hypF91 h1323 hH).F92_1.1.trans
    (pCoreOf_two_le_of_isSylowTwoOf (S.hypF91 h1323 hH).sylow_H)

theorem not_le_pCoreOf_of_not_elemAbelian {H : Subgroup G}
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) :
    ¬ conjClosure S.V3 H ≤ pCoreOf 2 (L ⊔ T) := fun h =>
  hna (S.elemAbelian_of_le_centralizer (h.trans (S.cLT ▸ inf_le_right)))

theorem almostSpecialA5Hyp (h1323 : Input1323Two) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) : AlmostSpecialA5Hyp S.V3 S.V1 L T H where
  base := (S.hypF91 h1323 hH).almostSpecialHyp
  natural := S.isA5ModuleFor
  card_V₁ := S.card_V1
  V_eq := by rw [S.conjClosure_V1_L, lOne_eq_L₁Of]; exact S.commutator_V_L1.symm
  U_ne := S.not_le_pCoreOf_of_not_elemAbelian hna

theorem T_le_normalizer_L1 : T ≤ Subgroup.normalizer (S.L1 : Set G) := by
  refine le_normalizer_oTwoRes_of_le_normalizer fun t ht => ?_
  have htN : t ∈ Subgroup.normalizer (S.V1 : Set G) := S.T_le_NV1 ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxL, hxN⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (S.T_le_NL ht) x).mp hxL, ?_⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ htN hxN) (Subgroup.inv_mem _ htN)
  · rintro ⟨hxL, hxN⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (S.T_le_NL ht) x).mpr hxL, ?_⟩
    have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ htN) hxN) htN
    simpa [mul_assoc] using this

theorem lemma_13_5_14_one (h1323 : Input1323Two) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hU : ⁅conjClosure S.V3 H, S.L1⁆ ⊔ S.V1 = conjClosure S.V3 H) :
    ⁅conjClosure S.V3 H, S.L1⁆ = conjClosure S.V3 H ∧ conjClosure S.V3 H ≤ S.L1 := by
  have hV1 : S.V1 ≤ ⁅conjClosure S.V3 H, S.L1⁆ :=
    S.V1_le_V3.trans (S.commutator_V3_L1.ge.trans
      (Subgroup.commutator_mono (le_conjClosure _ _) le_rfl))
  have h1 : ⁅conjClosure S.V3 H, S.L1⁆ = conjClosure S.V3 H :=
    calc ⁅conjClosure S.V3 H, S.L1⁆ = ⁅conjClosure S.V3 H, S.L1⁆ ⊔ S.V1 :=
          (sup_eq_left.mpr hV1).symm
      _ = conjClosure S.V3 H := hU
  refine ⟨h1, ?_⟩
  rw [← h1, Subgroup.commutator_le]
  intro u hu l hl
  have huN : u ∈ Subgroup.normalizer (S.L1 : Set G) :=
    S.T_le_normalizer_L1 (S.conjClosure_V3_le_T h1323 hH hu)
  have : u * l * u⁻¹ ∈ S.L1 := (Subgroup.mem_normalizer_iff.mp huN l).mp hl
  rw [commutatorElement_def]
  exact S.L1.mul_mem this (S.L1.inv_mem hl)

theorem rho_U_InD (h1323 : Input1323Two) {H : Subgroup G} (hH : H ∈ S.Hz) {u : G}
    (hu : u ∈ conjClosure S.V3 H) :
    InD (S.frame.ρ ⟨u, S.frame.T_le (S.conjClosure_V3_le_T h1323 hH hu)⟩) :=
  S.frame.T_D _ (S.conjClosure_V3_le_T h1323 hH hu)

theorem lemma_13_5_14_two (h1323 : Input1323Two) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) :
    (∀ u (hu : u ∈ conjClosure S.V3 H),
        InK4 (S.frame.ρ ⟨u, S.frame.T_le (S.conjClosure_V3_le_T h1323 hH hu)⟩)) ∧
      ∀ σ, InK4 σ → ∃ u, ∃ hu : u ∈ conjClosure S.V3 H,
        S.frame.ρ ⟨u, S.frame.T_le (S.conjClosure_V3_le_T h1323 hH hu)⟩ = σ := by
  have hUN : ∀ u ∈ conjClosure S.V3 H, u ∈ Subgroup.normalizer (V : Set G) := fun u hu =>
    S.frame.T_le (S.conjClosure_V3_le_T h1323 hH hu)
  have hL1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
  have hconj : ∀ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ S.L1 →
      ∀ u (hu : u ∈ conjClosure S.V3 H), ∃ hu' : (g : G) * u * (g : G)⁻¹ ∈ conjClosure S.V3 H,
        S.frame.ρ ⟨_, hUN _ hu'⟩ = S.frame.ρ g * S.frame.ρ ⟨u, hUN u hu⟩ * (S.frame.ρ g)⁻¹ := by
    intro g hg u hu
    have hu' := (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_conjClosure S.V3 H (hL1H hg)) u).mp hu
    refine ⟨hu', ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  obtain ⟨g, hgL1, hg⟩ := S.exists_L1_of_three c3p_props.1 c3p_props.2.1 c3p_props.2.2
  obtain ⟨g', hg'L1, hg'⟩ := S.exists_L1_of_three c3q_props.1 c3q_props.2.1 c3q_props.2.2
  have hgi : ((g⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ S.L1 := S.L1.inv_mem hgL1
  have hK4 : ∀ u (hu : u ∈ conjClosure S.V3 H), InK4 (S.frame.ρ ⟨u, hUN u hu⟩) := by
    intro u hu
    obtain ⟨h1, e1⟩ := hconj g hgL1 u hu
    obtain ⟨h2, e2⟩ := hconj g⁻¹ hgi u hu
    obtain ⟨h3, e3⟩ := hconj g' hg'L1 u hu
    have d1 := S.rho_U_InD h1323 hH h1
    have d2 := S.rho_U_InD h1323 hH h2
    have d3 := S.rho_U_InD h1323 hH h3
    rw [e1, hg] at d1
    rw [e2, map_inv, hg, inv_inv] at d2
    rw [e3, hg'] at d3
    exact InK4_of_conj_D _ (S.rho_U_InD h1323 hH hu) d1 d2 d3
  refine ⟨hK4, fun σ hσ => ?_⟩
  obtain ⟨u, hu, huC⟩ : ∃ u ∈ conjClosure S.V3 H, u ∉ Subgroup.centralizer (V : Set G) := by
    by_contra hall
    push Not at hall
    refine S.not_le_pCoreOf_of_not_elemAbelian hna fun x hx => ?_
    rw [← S.cLT]
    exact ⟨le_sup_right (a := L) (S.conjClosure_V3_le_T h1323 hH hx), hall x hx⟩
  have hu1 : S.frame.ρ ⟨u, hUN u hu⟩ ≠ 1 := fun h => huC (S.frame.mem_centralizer_of_rho _ h)
  rcases hσ with rfl | hσ
  · exact ⟨1, Subgroup.one_mem _, map_one _⟩
  have hσl : σ ∈ [pa, pb, pc] := by
    rcases hσ with rfl | rfl | rfl <;> simp
  have hul : S.frame.ρ ⟨u, hUN u hu⟩ ∈ [pa, pb, pc] := by
    rcases hK4 u hu with h | h | h | h
    · exact absurd h hu1
    all_goals simp [h]
  rcases K4_orbit _ hul σ hσl with h | h | h
  · exact ⟨u, hu, h.symm⟩
  · obtain ⟨h1, e1⟩ := hconj g hgL1 u hu
    exact ⟨_, h1, by rw [e1, hg, h]⟩
  · obtain ⟨h2, e2⟩ := hconj g⁻¹ hgi u hu
    exact ⟨_, h2, by rw [e2, map_inv, hg, inv_inv, h]⟩

theorem lemma_13_5_14_three (h1323 : Input1323Two) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) {l : G} (hl : l ∈ L)
    (hlN : l ∉ Subgroup.normalizer (S.V1 : Set G)) :
    conjClosure S.V3 H ⊔ rconj (conjClosure S.V3 H) l = L ⊔ conjClosure S.V3 H ∧
      S.L1 ≤ conjClosure S.V3 H ⊔ rconj (conjClosure S.V3 H) l := by
  have h2 := (S.almostSpecialA5Hyp h1323 hH hna).G24_two hl hlN
  exact ⟨h2, h2 ▸ S.L1_le_L.trans le_sup_left⟩

end Setting

end CFSG.Quasithin.H13.A5
