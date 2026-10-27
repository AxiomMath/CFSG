module

public import CFSG.Quasithin.H13.StatementsFSU
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.Quasithin.Background.F8Basic
public import CFSG.Quasithin.Background.G2A5

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

@[expose] def InD (σ : Equiv.Perm (Fin 5)) : Prop :=
  σ 4 = 4 ∧ (σ 0 : ℕ) / 2 = (σ 1 : ℕ) / 2

instance : DecidablePred InD := fun σ =>
  inferInstanceAs (Decidable (σ 4 = 4 ∧ (σ 0 : ℕ) / 2 = (σ 1 : ℕ) / 2))

@[expose] def InK4 (σ : Equiv.Perm (Fin 5)) : Prop :=
  σ = 1 ∨ σ = pa ∨ σ = pb ∨ σ = pc

instance : DecidablePred InK4 := fun σ =>
  inferInstanceAs (Decidable (σ = 1 ∨ σ = pa ∨ σ = pb ∨ σ = pc))

variable {G : Type} [Group G]

structure Frame (T L V : Subgroup G) where
  L_le : L ≤ Subgroup.normalizer (V : Set G)
  T_le : T ≤ Subgroup.normalizer (V : Set G)
  ψ : ↥V ≃* W5
  ρ : ↥(Subgroup.normalizer (V : Set G)) →* Equiv.Perm (Fin 5)
  equiv : ∀ (g : ↥(Subgroup.normalizer (V : Set G))) (v : ↥V),
    ψ (conjAct V g v) = pact (ρ g) (ψ v)
  image_L : ∀ σ : Equiv.Perm (Fin 5),
    (∃ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ L ∧ ρ g = σ) ↔ σ.sign = 1
  T_D : ∀ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ T → InD (ρ g)
  K4_T : ∀ σ : Equiv.Perm (Fin 5), InK4 σ →
    ∃ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ T ∧ ρ g = σ

structure Setting (G : Type) [Group G] [Finite G] (T L V : Subgroup G) where
  h13 : QTH13 G T L
  a5 : quasithinO2QuotientIso L (alternatingGroup (Fin 5))
  T_le_NL : T ≤ Subgroup.normalizer (L : Set G)
  maximal : quasithinIsMaximalLocal T L
  uniqueM : IsUniqueM (L ⊔ T) (Subgroup.normalizer (L : Set G))
  oTwoRes_L : oTwoRes L = L
  charTwo_L : CharTwo L
  reduced : IsTwoReducedIn (L ⊔ T) V
  cLT : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 (L ⊔ T)
  frame : Frame T L V
  irr : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V
  fsu : FSU G T L V

@[expose] def c4 : W5 →* Multiplicative (ZMod 2) where
  toFun x := Multiplicative.ofAdd (((Multiplicative.toAdd x : ↥Ev) : Fin 5 → ZMod 2) 4)
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def W3 : Subgroup W5 := c4.ker

theorem mem_W3 {x : W5} : x ∈ W3 ↔ c4 x = 1 := MonoidHom.mem_ker

theorem fixed_K4 : ∀ x : W5, (∀ σ : Equiv.Perm (Fin 5), InK4 σ → pact σ x = x) →
    x = 1 ∨ x = W4 := by
  decide +kernel

theorem pact_mem_W3 : ∀ (σ : Equiv.Perm (Fin 5)) (x : W5), σ 4 = 4 → c4 x = 1 →
    c4 (pact σ x) = 1 := by
  decide +kernel

theorem W4_mem_W3 : W4 ∈ W3 := mem_W3.2 (by decide +kernel)

theorem card_W3 : Nat.card W3 = 8 := by
  have : Fintype.card {x : W5 // c4 x = 1} = 8 := by decide +kernel
  rw [← this, ← Nat.card_eq_fintype_card]
  rfl

theorem card_W5 : Nat.card W5 = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem W3_gen : ∀ y x : W5, c4 y = 1 → y ≠ 1 → y ≠ W4 → c4 x = 1 →
    x ∈ [1, W4, y, y * W4, pact c3p y, pact c3p y * W4, y * pact c3p y,
      y * pact c3p y * W4] := by
  decide +kernel

theorem c3p_sign : c3p.sign = 1 := by decide

theorem c3p_four : c3p 4 = 4 := by decide

theorem c3p_cube : c3p ^ 3 = 1 := by decide

theorem c3p_pow_four_pow (a : ℕ) : c3p ^ (4 ^ a) = c3p := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ, pow_mul, ih]
    decide

theorem isSylowTwoOf_of_le {G : Type} [Group G] [Finite G] {T H : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hTH : T ≤ H) : IsSylowTwoOf T H :=
  ⟨hTH, hT.1, fun h => hT.2 (h.trans (by
    simpa [Subgroup.relIndex] using Subgroup.relIndex_dvd_index_of_le hTH))⟩

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem isPGroup_T : IsPGroup 2 T := S.h13.sylow.1

theorem sylow_top : IsSylowTwoOf T ⊤ := isSylowTwoOf_of_le S.h13.sylow le_top

theorem sylow_LT : IsSylowTwoOf T (L ⊔ T) := isSylowTwoOf_of_le S.h13.sylow le_sup_right

theorem elemAbelian_V : IsElemAbelian 2 V := S.reduced.2.2.1

theorem isPGroup_V : IsPGroup 2 V := fun g =>
  ⟨1, Subtype.ext (by simpa using S.elemAbelian_V.2 g g.2)⟩

theorem V_le_pCoreOf_LT : V ≤ pCoreOf 2 (L ⊔ T) :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 S.reduced.1 S.reduced.2.1 S.isPGroup_V

theorem pCoreOf_LT_le_T : pCoreOf 2 (L ⊔ T) ≤ T := by
  obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo S.h13.sylow
  have := pCoreOf_two_le_sylow (L ⊔ T) P (hP ▸ le_sup_right)
  rwa [hP] at this

theorem V_le_T : V ≤ T := S.V_le_pCoreOf_LT.trans S.pCoreOf_LT_le_T

theorem cT : T ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 (L ⊔ T) := by
  apply le_antisymm
  · rw [← S.cLT]
    exact inf_le_inf_right _ le_sup_right
  · exact le_inf S.pCoreOf_LT_le_T (S.cLT ▸ inf_le_right)

theorem isTwoLocal_NV : IsTwoLocal (Subgroup.normalizer (V : Set G)) := by
  refine ⟨V, ?_, S.isPGroup_V, rfl⟩
  intro h
  have := S.frame.ψ.toEquiv
  rw [h] at this
  have hcard := Nat.card_congr this
  have h16 : Nat.card W5 = 16 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [h16] at hcard
  simp at hcard

theorem NV_le_M : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨M', hM', hM'le⟩ := exists_maxTwoLocal_ge S.isTwoLocal_NV
  have h := S.uniqueM.2 M' ⟨hM', S.reduced.2.1.trans hM'le⟩
  exact h ▸ hM'le

theorem psi_conj (g : ↥(Subgroup.normalizer (V : Set G))) (v : ↥V) :
    S.frame.ψ ⟨(g : G) * v * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp g.2 v).mp v.2⟩ =
      pact (S.frame.ρ g) (S.frame.ψ v) := by
  rw [← S.frame.equiv]
  congr 1

theorem conj_eq_iff (g : ↥(Subgroup.normalizer (V : Set G))) (v : ↥V) :
    (g : G) * v * (g : G)⁻¹ = v ↔ pact (S.frame.ρ g) (S.frame.ψ v) = S.frame.ψ v := by
  rw [← S.psi_conj]
  constructor
  · intro h
    congr 1
    exact Subtype.ext h
  · intro h
    have := congrArg Subtype.val (S.frame.ψ.injective h)
    simpa using this

@[expose] noncomputable def pre (Y : Subgroup W5) : Subgroup G :=
  (Y.comap S.frame.ψ.toMonoidHom).map V.subtype

theorem mem_pre {Y : Subgroup W5} {x : G} :
    x ∈ S.pre Y ↔ ∃ h : x ∈ V, S.frame.ψ ⟨x, h⟩ ∈ Y := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.2, hv⟩
  · rintro ⟨h, hY⟩
    exact ⟨⟨x, h⟩, hY, rfl⟩

theorem pre_le_V (Y : Subgroup W5) : S.pre Y ≤ V := Subgroup.map_subtype_le _

theorem pre_mono {Y Y' : Subgroup W5} (h : Y ≤ Y') : S.pre Y ≤ S.pre Y' :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem card_pre (Y : Subgroup W5) : Nat.card (S.pre Y) = Nat.card Y := by
  unfold pre
  rw [Subgroup.card_map_of_injective V.subtype_injective]
  exact Nat.card_congr ((Y.equivMapOfInjective S.frame.ψ.symm.toMonoidHom
    S.frame.ψ.symm.injective).toEquiv.trans (Equiv.subtypeEquivRight fun v => by
      constructor
      · rintro ⟨y, hy, rfl⟩
        show S.frame.ψ (S.frame.ψ.symm y) ∈ Y
        simpa using hy
      · intro hv
        exact ⟨S.frame.ψ v, hv, by simp⟩)).symm

@[expose] noncomputable def z : G := (S.frame.ψ.symm W4 : G)

@[expose] noncomputable def V1 : Subgroup G := Subgroup.zpowers S.z

@[expose] noncomputable def V3 : Subgroup G := S.pre W3

theorem z_mem_V : S.z ∈ V := (S.frame.ψ.symm W4).2

theorem psi_z : S.frame.ψ ⟨S.z, S.z_mem_V⟩ = W4 := by
  have : (⟨S.z, S.z_mem_V⟩ : ↥V) = S.frame.ψ.symm W4 := Subtype.ext rfl
  rw [this, MulEquiv.apply_symm_apply]

theorem z_ne_one : S.z ≠ 1 := by
  intro h
  have h1 : S.frame.ψ ⟨S.z, S.z_mem_V⟩ = 1 := by
    have : (⟨S.z, S.z_mem_V⟩ : ↥V) = 1 := Subtype.ext h
    rw [this, map_one]
  rw [S.psi_z] at h1
  exact W4_ne_one h1

theorem z_sq : S.z ^ 2 = 1 := S.elemAbelian_V.2 _ S.z_mem_V

theorem orderOf_z : orderOf S.z = 2 :=
  orderOf_eq_prime S.z_sq S.z_ne_one

theorem card_V1 : Nat.card S.V1 = 2 := by
  unfold V1
  rw [Nat.card_zpowers, S.orderOf_z]

theorem mem_V1 {x : G} : x ∈ S.V1 ↔ x = 1 ∨ x = S.z := by
  unfold V1
  rw [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    have h := zpow_mod_orderOf S.z k
    rw [S.orderOf_z, Nat.cast_ofNat] at h
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left
      rw [← h, hk, zpow_zero]
    · right
      rw [← h, hk, zpow_one]
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

theorem V1_le_V : S.V1 ≤ V := by
  unfold V1
  rw [Subgroup.zpowers_le]
  exact S.z_mem_V

theorem V3_le_V : S.V3 ≤ V := S.pre_le_V W3

theorem z_mem_V3 : S.z ∈ S.V3 := S.mem_pre.2 ⟨S.z_mem_V, by rw [S.psi_z]; exact W4_mem_W3⟩

theorem V1_le_V3 : S.V1 ≤ S.V3 := by
  unfold V1
  rw [Subgroup.zpowers_le]
  exact S.z_mem_V3

theorem card_V3 : Nat.card S.V3 = 8 := by
  rw [V3, S.card_pre, card_W3]

theorem card_V : Nat.card V = 16 := by
  rw [Nat.card_congr S.frame.ψ.toEquiv, card_W5]

theorem V1_lt_V3 : S.V1 < S.V3 := by
  refine lt_of_le_of_ne S.V1_le_V3 fun h => ?_
  have := S.card_V3
  rw [← h, S.card_V1] at this
  omega

theorem conj_z_of_mem_T {t : G} (ht : t ∈ T) : t * S.z * t⁻¹ = S.z := by
  have h := (S.conj_eq_iff ⟨t, S.frame.T_le ht⟩ ⟨S.z, S.z_mem_V⟩).2
  rw [S.psi_z] at h
  exact h (pact_W4 (S.frame.T_D ⟨t, S.frame.T_le ht⟩ ht).1)

theorem mem_V1_of_fixed {v : G} (hv : v ∈ V) (hfix : ∀ t ∈ T, t * v * t⁻¹ = v) : v ∈ S.V1 := by
  rw [S.mem_V1]
  have : ∀ σ : Equiv.Perm (Fin 5), InK4 σ → pact σ (S.frame.ψ ⟨v, hv⟩) = S.frame.ψ ⟨v, hv⟩ := by
    intro σ hσ
    obtain ⟨g, hgT, rfl⟩ := S.frame.K4_T σ hσ
    exact (S.conj_eq_iff g ⟨v, hv⟩).1 (hfix g hgT)
  rcases fixed_K4 _ this with h | h
  · left
    have : (⟨v, hv⟩ : ↥V) = 1 := S.frame.ψ.injective (by rw [h, map_one])
    exact congrArg Subtype.val this
  · right
    have : (⟨v, hv⟩ : ↥V) = ⟨S.z, S.z_mem_V⟩ := S.frame.ψ.injective (by rw [h, S.psi_z])
    exact congrArg Subtype.val this

theorem evenChar : CFSG.Open.quasithinEvenCharacteristic G := S.h13.qtke.2.1

theorem charTwo_of_inH {H : Subgroup G} (hH : InH T H) : CharTwo H := by
  obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo S.h13.sylow
  subst hP
  exact CFSG.Quasithin.charTwo_of_inH S.evenChar P hH

theorem le_normalizer_pre {Y : Subgroup W5} {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G))
    (hY : ∀ y ∈ Y, pact (S.frame.ρ ⟨g, hg⟩) y ∈ Y)
    (hY' : ∀ y ∈ Y, pact (S.frame.ρ ⟨g, hg⟩)⁻¹ y ∈ Y) :
    g ∈ Subgroup.normalizer (S.pre Y : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨hxV, hxY⟩ := S.mem_pre.1 hx
    refine S.mem_pre.2 ⟨(Subgroup.mem_normalizer_iff.mp hg x).mp hxV, ?_⟩
    rw [S.psi_conj ⟨g, hg⟩ ⟨x, hxV⟩]
    exact hY _ hxY
  · intro hx
    obtain ⟨hxV, hxY⟩ := S.mem_pre.1 hx
    have hxV' : x ∈ V := (Subgroup.mem_normalizer_iff.mp hg x).mpr hxV
    refine S.mem_pre.2 ⟨hxV', ?_⟩
    have h := S.psi_conj ⟨g, hg⟩ ⟨x, hxV'⟩
    have : S.frame.ψ ⟨x, hxV'⟩ = pact (S.frame.ρ ⟨g, hg⟩)⁻¹
        (S.frame.ψ ⟨g * x * g⁻¹, hxV⟩) := by
      rw [h, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
    rw [this]
    exact hY' _ hxY

theorem le_normalizer_V3 {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G))
    (h4 : S.frame.ρ ⟨g, hg⟩ 4 = 4) : g ∈ Subgroup.normalizer (S.V3 : Set G) := by
  refine S.le_normalizer_pre hg (fun y hy => mem_W3.2 (pact_mem_W3 _ y h4 (mem_W3.1 hy)))
    (fun y hy => mem_W3.2 (pact_mem_W3 _ y ?_ (mem_W3.1 hy)))
  rw [Equiv.Perm.inv_eq_iff_eq, h4]

theorem rho_four_of_conj_z {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G))
    (hz : g * S.z * g⁻¹ = S.z) : S.frame.ρ ⟨g, hg⟩ 4 = 4 := by
  have h := (S.conj_eq_iff ⟨g, hg⟩ ⟨S.z, S.z_mem_V⟩).1 hz
  rw [S.psi_z] at h
  exact fix_four_of_pact_W4 h

theorem conj_z_of_normalizes {g : G} (hg : g ∈ Subgroup.normalizer (S.V1 : Set G)) :
    g * S.z * g⁻¹ = S.z := by
  have hmem : g * S.z * g⁻¹ ∈ S.V1 :=
    (Subgroup.mem_normalizer_iff.mp hg S.z).mp (S.mem_V1.2 (Or.inr rfl))
  rcases S.mem_V1.1 hmem with h | h
  · exfalso
    apply S.z_ne_one
    have : g⁻¹ * (g * S.z * g⁻¹) * g = S.z := by group
    rw [h] at this
    simpa using this.symm
  · exact h

theorem normalizer_V1 : Subgroup.normalizer (S.V1 : Set G) =
    Subgroup.centralizer ({S.z} : Set G) := by
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := S.conj_z_of_normalizes hg
    calc g * S.z = g * S.z * g⁻¹ * g := by group
      _ = S.z * g := by rw [this]
  · intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [S.mem_V1]
    constructor
    · rintro (rfl | rfl)
      · left; group
      · right
        calc g * S.z * g⁻¹ = S.z * g * g⁻¹ := by rw [hg]
          _ = S.z := by group
    · rintro (h | h)
      · left
        have : g⁻¹ * (g * x * g⁻¹) * g = x := by group
        rw [h] at this
        simpa using this.symm
      · right
        have h1 : g⁻¹ * (g * x * g⁻¹) * g = x := by group
        have h2 : g⁻¹ * S.z * g = S.z := by
          calc g⁻¹ * S.z * g = g⁻¹ * (g * S.z) := by rw [hg]; group
            _ = S.z := by group
        rw [h, h2] at h1
        exact h1.symm

theorem T_le_NV1 : T ≤ Subgroup.normalizer (S.V1 : Set G) := by
  intro t ht
  rw [S.normalizer_V1, Subgroup.mem_centralizer_singleton_iff]
  have := S.conj_z_of_mem_T ht
  calc t * S.z = t * S.z * t⁻¹ * t := by group
    _ = S.z * t := by rw [this]

theorem T_le_NV3 : T ≤ Subgroup.normalizer (S.V3 : Set G) := fun _ ht =>
  S.le_normalizer_V3 (S.frame.T_le ht) (S.rho_four_of_conj_z _ (S.conj_z_of_mem_T ht))

@[expose] noncomputable def L1 : Subgroup G := L₁Of L S.V1

theorem L1_le : S.L1 ≤ L ⊓ Subgroup.normalizer (S.V1 : Set G) := oTwoRes_le _

theorem L1_le_L : S.L1 ≤ L := S.L1_le.trans inf_le_left

theorem L1_le_NV1 : S.L1 ≤ Subgroup.normalizer (S.V1 : Set G) := S.L1_le.trans inf_le_right

theorem NLV1_le_NV3 : L ⊓ Subgroup.normalizer (S.V1 : Set G) ≤
    Subgroup.normalizer (S.V3 : Set G) := fun _ hl =>
  S.le_normalizer_V3 (S.frame.L_le hl.1)
    (S.rho_four_of_conj_z _ (S.conj_z_of_normalizes hl.2))

theorem L1T_le_NV3 : S.L1 ⊔ T ≤ Subgroup.normalizer (S.V3 : Set G) :=
  sup_le (S.L1_le.trans S.NLV1_le_NV3) S.T_le_NV3

theorem L1T_le_NV1 : S.L1 ⊔ T ≤ Subgroup.normalizer (S.V1 : Set G) :=
  sup_le S.L1_le_NV1 S.T_le_NV1

@[expose] noncomputable def img (W : Subgroup G) : Subgroup W5 :=
  (W.subgroupOf V).map S.frame.ψ.toMonoidHom

theorem mem_img_iff {W : Subgroup G} (v : ↥V) : S.frame.ψ v ∈ S.img W ↔ (v : G) ∈ W := by
  constructor
  · rintro ⟨u, hu, huv⟩
    have : u = v := S.frame.ψ.injective huv
    rw [← this]
    exact hu
  · intro h
    exact ⟨v, h, rfl⟩

theorem pact_mem_img {W : Subgroup G} (g : ↥(Subgroup.normalizer (V : Set G)))
    (hgW : (g : G) ∈ Subgroup.normalizer (W : Set G)) {y : W5} (hy : y ∈ S.img W) :
    pact (S.frame.ρ g) y ∈ S.img W := by
  obtain ⟨v, rfl⟩ := S.frame.ψ.surjective y
  rw [S.mem_img_iff] at hy
  rw [← S.psi_conj g v, S.mem_img_iff]
  exact (Subgroup.mem_normalizer_iff.mp hgW v).mp hy

theorem exists_L1_c3p : ∃ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ S.L1 ∧
    S.frame.ρ g = c3p := by
  obtain ⟨g, hgL, hg⟩ := (S.frame.image_L c3p).2 c3p_sign
  have hgz : (g : G) * S.z * (g : G)⁻¹ = S.z := by
    rw [S.conj_eq_iff g ⟨S.z, S.z_mem_V⟩, S.psi_z, hg]
    exact pact_W4 c3p_four
  have hgN : (g : G) ∈ L ⊓ Subgroup.normalizer (S.V1 : Set G) := by
    refine ⟨hgL, ?_⟩
    show (g : G) ∈ Subgroup.normalizer (S.V1 : Set G)
    rw [S.normalizer_V1, Subgroup.mem_centralizer_singleton_iff]
    calc (g : G) * S.z = (g : G) * S.z * (g : G)⁻¹ * g := by group
      _ = S.z * g := by rw [hgz]
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  refine ⟨g ^ (4 ^ a), ?_, by rw [map_pow, hg, c3p_pow_four_pow]⟩
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

theorem irred_V3 (W : Subgroup G) (h1 : S.V1 ≤ W) (h3 : W ≤ S.V3)
    (hN : S.L1 ⊔ T ≤ Subgroup.normalizer (W : Set G)) : W = S.V1 ∨ W = S.V3 := by
  by_cases hW : W ≤ S.V1
  · exact Or.inl (le_antisymm hW h1)
  right
  refine le_antisymm h3 fun x hx => ?_
  obtain ⟨w, hwW, hwV1⟩ := IsConcreteLE.not_le_iff_exists.1 hW
  have hwV : w ∈ V := S.V3_le_V (h3 hwW)
  have hxV : x ∈ V := S.V3_le_V hx
  obtain ⟨_, hy3⟩ := S.mem_pre.1 (h3 hwW)
  obtain ⟨_, hx3⟩ := S.mem_pre.1 hx
  set y := S.frame.ψ ⟨w, hwV⟩ with hy
  have hy1 : y ≠ 1 := fun h => hwV1 (by
    have : (⟨w, hwV⟩ : ↥V) = 1 := S.frame.ψ.injective (by rw [← hy, h, map_one])
    rw [S.mem_V1]
    exact Or.inl (congrArg Subtype.val this))
  have hyW : y ≠ W4 := fun h => hwV1 (by
    have : (⟨w, hwV⟩ : ↥V) = ⟨S.z, S.z_mem_V⟩ := S.frame.ψ.injective (by rw [← hy, h, S.psi_z])
    rw [S.mem_V1]
    exact Or.inr (congrArg Subtype.val this))
  obtain ⟨g, hgL1, hg⟩ := S.exists_L1_c3p
  have hgW : (g : G) ∈ Subgroup.normalizer (W : Set G) := hN (le_sup_left (a := S.L1) hgL1)
  have hyI : y ∈ S.img W := (S.mem_img_iff _).2 hwW
  have hzI : W4 ∈ S.img W := by
    rw [← S.psi_z, S.mem_img_iff]
    exact h1 (S.mem_V1.2 (Or.inr rfl))
  have hcI : pact c3p y ∈ S.img W := hg ▸ S.pact_mem_img g hgW hyI
  have hmem := W3_gen y (S.frame.ψ ⟨x, hxV⟩) (mem_W3.1 hy3) hy1 hyW (mem_W3.1 hx3)
  refine (S.mem_img_iff ⟨x, hxV⟩).1 ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h <;> rw [h]
  · exact (S.img W).one_mem
  · exact hzI
  · exact hyI
  · exact (S.img W).mul_mem hyI hzI
  · exact hcI
  · exact (S.img W).mul_mem hcI hzI
  · exact (S.img W).mul_mem hyI hcI
  · exact (S.img W).mul_mem ((S.img W).mul_mem hyI hcI) hzI

end Setting

end CFSG.Quasithin.H13.A5
