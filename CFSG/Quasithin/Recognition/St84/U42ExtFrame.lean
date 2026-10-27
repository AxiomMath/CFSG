module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.UAmalCoordsPlain
public import CFSG.GH74.QTGen4.U42.MSplitGenF
public import CFSG.GH74.QTGen4.DSGen4.Statements

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
  CFSG.GH74.QTGen4.DSGen4 CFSG.GH74.QTGen4.U42
  CFSG.Quasithin.H13.A5 CFSG.Quasithin.A5Model CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

@[expose] def U42ExtFrame (L1 L2 S : Subgroup G) : Prop :=
  ∃ C : CoordData ↥(L1 ⊔ bigB L1 L2 S),
    C.V = (pCoreOf 2 L1).subgroupOf (L1 ⊔ bigB L1 L2 S) ∧
    C.ρ.range = ⊤ ∧
    (∀ m : ↥(L1 ⊔ bigB L1 L2 S), (m : G) ∈ S ↔ InD (C.ρ m)) ∧
    (∀ m : ↥(L1 ⊔ bigB L1 L2 S), (m : G) ∈ bigB L1 L2 S ↔ (C.ρ m) 4 = 4) ∧
    (∃ A : Subgroup ↥(L1 ⊔ bigB L1 L2 S), A ⊓ C.V = ⊥ ∧ C.V ⊔ A = ⊤) ∧
    Nat.card ↥S = 128

theorem dsuce_card_perm5 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
  rw [Nat.card_perm, Nat.card_fin]
  norm_num

theorem dsuce_card_alt5 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup]
  norm_num

theorem dsuce_card_of_sylow [Finite G] {H S : Subgroup G} (hSH : S ≤ H)
    (hp : IsPGroup 2 S) (hodd : ¬ 2 ∣ (S.subgroupOf H).index)
    {m : ℕ} (hH : Nat.card ↥H = 2 ^ m * 15) : Nat.card ↥S = 2 ^ m := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  have hsub : Nat.card ↥(S.subgroupOf H) = Nat.card ↥S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSH).toEquiv
  have hmul := Subgroup.card_mul_index (S.subgroupOf H)
  rw [hsub, hn, hH] at hmul
  have hdvd : (S.subgroupOf H).index ∣ 2 ^ m * 15 :=
    ⟨2 ^ n, hmul.symm.trans (mul_comm (2 ^ n) (S.subgroupOf H).index)⟩
  have hcop0 : Nat.Coprime 2 (S.subgroupOf H).index :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd
  have hcop : Nat.Coprime (S.subgroupOf H).index (2 ^ m) := hcop0.symm.pow_right m
  have hidx15 : (S.subgroupOf H).index ∣ 15 := by
    apply hcop.dvd_of_dvd_mul_left
    exact hdvd
  have hidxle : (S.subgroupOf H).index ≤ 15 := Nat.le_of_dvd (by norm_num) hidx15
  have hidxpos : 0 < (S.subgroupOf H).index := Nat.pos_of_ne_zero (by
    intro h0
    rw [h0] at hmul
    omega)
  interval_cases h : (S.subgroupOf H).index
  · have h2n : 2 ^ n = 2 ^ m * 15 := by simpa using hmul
    have h3 : (3 : ℕ) ∣ 2 ^ n := by rw [h2n]; exact ⟨2 ^ m * 5, by ring⟩
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) h3
    norm_num at this
  · exfalso; norm_num at hidx15
  · have h2n : 2 ^ n = 2 ^ m * 5 := by
      apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 3)
      calc 2 ^ n * 3 = 2 ^ m * 15 := hmul
        _ = (2 ^ m * 5) * 3 := by ring
    have h5 : (5 : ℕ) ∣ 2 ^ n := by rw [h2n]; exact ⟨2 ^ m, by ring⟩
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h5
    norm_num at this
  · exfalso; norm_num at hidx15
  · have h2n : 2 ^ n = 2 ^ m * 3 := by
      apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 5)
      calc 2 ^ n * 5 = 2 ^ m * 15 := hmul
        _ = (2 ^ m * 3) * 5 := by ring
    have h3 : (3 : ℕ) ∣ 2 ^ n := by rw [h2n]; exact ⟨2 ^ m, by ring⟩
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) h3
    norm_num at this
  · exfalso; norm_num at hidx15
  · exfalso; norm_num at hidx15
  · exfalso; norm_num at hidx15
  · exfalso; norm_num at hidx15
  · exfalso; norm_num at hidx15
  · exfalso; norm_num at hidx15
  · exfalso; norm_num at hidx15
  · exfalso; norm_num at hidx15
  · exfalso; norm_num at hidx15
  · have h2n : 2 ^ n = 2 ^ m := by
      apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 15)
      exact hmul
    rw [hn, Nat.pow_right_injective (by norm_num : 2 ≤ 2) h2n]

theorem dsuce_card_P1 [Finite G] {L1 L2 S : Subgroup G}
    (hE1 : pCoreOf 2 L1 = dsQ L1 L2 S) (hE16 : Nat.card ↥(pCoreOf 2 L1) = 16)
    (h5 : Nonempty (oTwoQuot ↥(L1 ⊔ bigB L1 L2 S) ≃* Equiv.Perm (Fin 5))) :
    Nat.card ↥(L1 ⊔ bigB L1 L2 S) = 1920 := by
  classical
  obtain ⟨e5⟩ := h5
  have hpc : Nat.card ↥(CFSG.pCore 2 ↥(L1 ⊔ bigB L1 L2 S)) = 16 := by
    rw [← hE16]
    rw [show pCoreOf 2 L1 = pCoreOf 2 (L1 ⊔ bigB L1 L2 S) from hE1]
    exact (Subgroup.card_map_of_injective (K := CFSG.pCore 2 ↥(L1 ⊔ bigB L1 L2 S))
      (f := (L1 ⊔ bigB L1 L2 S).subtype) (Subgroup.subtype_injective _)).symm
  have hquot : Nat.card (↥(L1 ⊔ bigB L1 L2 S) ⧸
      CFSG.pCore 2 ↥(L1 ⊔ bigB L1 L2 S)) = 120 := by
    rw [Nat.card_congr e5.toEquiv, dsuce_card_perm5]
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (CFSG.pCore 2 ↥(L1 ⊔ bigB L1 L2 S))
  rw [hquot, hpc] at hmul
  omega

theorem dsuce_card_L1 [Finite G] {L1 : Subgroup G} (halt : IsAltType L1 5)
    (hE16 : Nat.card ↥(pCoreOf 2 L1) = 16) : Nat.card ↥L1 = 960 := by
  obtain ⟨α, hαs, hαk, -⟩ := halt
  have hker : Nat.card ↥(CFSG.pCore 2 ↥L1) = 16 := by
    rw [← hE16]
    exact (Subgroup.card_map_of_injective (K := CFSG.pCore 2 ↥L1) (f := L1.subtype)
      (Subgroup.subtype_injective L1)).symm
  have hrange : α.range = ⊤ := MonoidHom.range_eq_top.mpr hαs
  have h := Subgroup.card_ker_mul_card_range α
  rw [hαk] at h
  rw [hker, hrange, Subgroup.card_top, dsuce_card_alt5] at h
  omega

theorem dsuce_card_S [Finite G] {L1 L2 S : Subgroup G}
    (hE1 : pCoreOf 2 L1 = dsQ L1 L2 S) (hE16 : Nat.card ↥(pCoreOf 2 L1) = 16)
    (h5 : Nonempty (oTwoQuot ↥(L1 ⊔ bigB L1 L2 S) ≃* Equiv.Perm (Fin 5)))
    (hsylS : IsSylowTwoOf S (L1 ⊔ bigB L1 L2 S)) : Nat.card ↥S = 128 := by
  have h := dsuce_card_of_sylow hsylS.1 hsylS.2.1 hsylS.2.2
    (m := 7) (by rw [dsuce_card_P1 hE1 hE16 h5]; norm_num)
  rwa [show (2 : ℕ) ^ 7 = 128 by norm_num] at h

theorem dsuce_card_Sinf [Finite G] {L1 L2 S : Subgroup G} (h : Hyp111R L1 L2 S)
    (hb6 : F112B6Loc L2 L1) (hE16 : Nat.card ↥(pCoreOf 2 L1) = 16) :
    Nat.card ↥(S ⊓ L1) = 64 := by
  obtain ⟨-, -, -, -, -, halt⟩ := hb6
  have := dsuce_card_of_sylow (H := L1) inf_le_right h.hyp.h1.sylow.2.1
    h.hyp.h1.sylow.2.2 (m := 6) (by
      rw [dsuce_card_L1 halt hE16]; norm_num)
  rwa [show (2 : ℕ) ^ 6 = 64 by norm_num] at this

@[expose] noncomputable def dsuce_relabel {M : Type*} [Group M] (C : CoordData M)
    (τ : Equiv.Perm (Fin 5)) : CoordData M where
  V := C.V
  hV := C.hV
  ψ := C.ψ.trans (pact τ)
  ρ := (MulAut.conj τ).toMonoidHom.comp C.ρ
  ker_ρ := by
    rw [← C.ker_ρ]
    ext m
    simp only [MonoidHom.mem_ker]
    constructor
    · intro h
      exact (MulAut.conj τ).injective (by simpa using h)
    · intro h
      show (MulAut.conj τ) (C.ρ m) = 1
      rw [h, map_one]
  conj_ψ := by
    intro m v
    have h := C.conj_ψ m v
    show pact τ (C.ψ ⟨m * (v : M) * m⁻¹, _⟩) =
      pact (τ * C.ρ m * τ⁻¹) (pact τ (C.ψ v))
    rw [h]
    exact (dsucp_pact_conj τ (C.ρ m) (C.ψ v)).symm

theorem dsuce_relabel_V {M : Type*} [Group M] (C : CoordData M) (τ : Equiv.Perm (Fin 5)) :
    (dsuce_relabel C τ).V = C.V := rfl

theorem dsuce_relabel_range {M : Type*} [Group M] (C : CoordData M) (τ : Equiv.Perm (Fin 5))
    (hR : C.ρ.range = ⊤) : (dsuce_relabel C τ).ρ.range = ⊤ := by
  rw [show (dsuce_relabel C τ).ρ = (MulAut.conj τ).toMonoidHom.comp C.ρ from rfl,
    MonoidHom.range_comp, hR, Subgroup.map_top_of_surjective _ (MulAut.conj τ).surjective]

theorem dsuce_relabel_map {M : Type*} [Group M] (C : CoordData M) (τ : Equiv.Perm (Fin 5))
    (T : Subgroup M) : T.map (dsuce_relabel C τ).ρ =
      (T.map C.ρ).map (MulAut.conj τ).toMonoidHom := by
  rw [show (dsuce_relabel C τ).ρ = (MulAut.conj τ).toMonoidHom.comp C.ρ from rfl,
    Subgroup.map_map]

def dsuceK4 : Subgroup (Equiv.Perm (Fin 5)) where
  carrier := {σ | InK4 σ}
  one_mem' := Or.inl rfl
  mul_mem' := by
    have key : ∀ a b : Equiv.Perm (Fin 5), InK4 a → InK4 b → InK4 (a * b) := by
      decide +kernel
    exact fun {a b} ha hb => key a b ha hb
  inv_mem' := by
    have key : ∀ a : Equiv.Perm (Fin 5), InK4 a → InK4 a⁻¹ := by
      decide +kernel
    exact fun {a} ha => key a ha

theorem dsuce_card_K4 : Nat.card dsuceK4 = 4 := by
  have : Fintype.card {σ : Equiv.Perm (Fin 5) // InK4 σ} = 4 := by decide +kernel
  rw [← this, ← Nat.card_eq_fintype_card]
  rfl

theorem dsuce_norm_K4_iff : ∀ σ : Equiv.Perm (Fin 5),
    (∀ k : Equiv.Perm (Fin 5), InK4 k → InK4 (σ * k * σ⁻¹)) ↔ σ 4 = 4 := by
  decide +kernel

theorem dsuce_mem_normalizer_K4_iff (σ : Equiv.Perm (Fin 5)) :
    σ ∈ Subgroup.normalizer (dsuceK4 : Set (Equiv.Perm (Fin 5))) ↔ σ 4 = 4 := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h
    exact (dsuce_norm_K4_iff σ).mp fun k hk => (h k).mp hk
  · intro h4 k
    constructor
    · intro hk
      exact (dsuce_norm_K4_iff σ).mpr h4 k hk
    · intro hk
      have h4inv : (σ⁻¹) 4 = 4 := by
        rw [Equiv.Perm.inv_eq_iff_eq]
        exact h4.symm
      have hthis := (dsuce_norm_K4_iff σ⁻¹).mpr h4inv (σ * k * σ⁻¹) hk
      change InK4 k
      simpa [mul_assoc] using hthis

theorem dsuce_fix_alt : ∀ x : W5,
    (∀ σ : Equiv.Perm (Fin 5), σ.sign = 1 → pact σ x = x) → x = 1 := by
  decide +kernel

theorem dsuce_normalizer_map_iff {M : Type*} [Group M] (ρ : M →* Equiv.Perm (Fin 5))
    {V T : Subgroup M} (hker : ρ.ker = V) (hVT : V ≤ T) (m : M) :
    m ∈ Subgroup.normalizer (T : Set M) ↔
      ρ m ∈ Subgroup.normalizer (T.map ρ : Set (Equiv.Perm (Fin 5))) := by
  have hstep : ∀ n : M, ρ n ∈ Subgroup.normalizer (T.map ρ : Set (Equiv.Perm (Fin 5))) →
      ∀ y ∈ T, n * y * n⁻¹ ∈ T := by
    intro n hn y hy
    have h1 : ρ (n * y * n⁻¹) ∈ T.map ρ := by
      rw [map_mul, map_inv, map_mul]
      exact (Subgroup.mem_normalizer_iff.mp hn (ρ y)).mp ⟨y, hy, rfl⟩
    obtain ⟨t, ht, htm⟩ := h1
    have h2 : n * y * n⁻¹ * t⁻¹ ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, htm, mul_inv_cancel]
    have h3 : n * y * n⁻¹ * t⁻¹ ∈ T := by
      rw [hker] at h2
      exact hVT h2
    have h4 : n * y * n⁻¹ = (n * y * n⁻¹ * t⁻¹) * t := by group
    rw [h4]
    exact T.mul_mem h3 ht
  constructor
  · intro hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨m * t * m⁻¹, (Subgroup.mem_normalizer_iff.mp hm t).mp ht, by simp⟩
    · rintro ⟨t, ht, htm⟩
      have hminv : m⁻¹ ∈ Subgroup.normalizer (T : Set M) :=
        (Subgroup.normalizer (T : Set M)).inv_mem hm
      have hx : x = ρ (m⁻¹ * t * m) := by
        rw [map_mul, map_mul, map_inv, htm]
        group
      rw [hx]
      exact ⟨m⁻¹ * t * m, by simpa using (Subgroup.mem_normalizer_iff.mp hminv t).mp ht, rfl⟩
  · intro hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hstep m hm x hx
    · intro hx
      have hminv : ρ m⁻¹ ∈ Subgroup.normalizer (T.map ρ : Set (Equiv.Perm (Fin 5))) := by
        rw [map_inv]
        exact (Subgroup.normalizer (T.map ρ : Set (Equiv.Perm (Fin 5)))).inv_mem hm
      have := hstep m⁻¹ hminv (m * x * m⁻¹) hx
      simpa [mul_assoc] using this

theorem dsuce_complement_conj {M : Type*} [Group M] [Finite M] (C : CoordData M)
    (hR : C.ρ.range = alternatingGroup (Fin 5)) {A B : Subgroup M}
    (hAV : A ⊓ C.V = ⊥) (hAL : C.V ⊔ A = ⊤) (hBV : B ⊓ C.V = ⊥) (hBL : C.V ⊔ B = ⊤) :
    ∃ w ∈ C.V, ∀ x : M, x ∈ B ↔ w⁻¹ * x * w ∈ A := by
  classical
  haveI hVnormal : C.V.Normal := C.hV
  have one_sign : (1 : Equiv.Perm (Fin 5)).sign = 1 := by simp
  have eq_of_rho_eq : ∀ {K : Subgroup M}, K ⊓ C.V = ⊥ → ∀ {x y : M}, x ∈ K → y ∈ K →
      C.ρ x = C.ρ y → x = y := by
    intro K hKV x y hx hy h
    have h1 : C.ρ (x * y⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
    have h2 : x * y⁻¹ ∈ C.V := C.mem_of_rho_eq_one h1
    have h3 : x * y⁻¹ ∈ K ⊓ C.V := ⟨K.mul_mem hx (K.inv_mem hy), h2⟩
    rw [hKV] at h3
    exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp h3)
  have exists_rg : ∀ (K : Subgroup M), C.V ⊔ K = ⊤ → ∀ {σ : Equiv.Perm (Fin 5)}, σ.sign = 1 →
      ∃ a ∈ K, C.ρ a = σ := by
    intro K hK σ hσ
    have hσ' : σ ∈ C.ρ.range := by rw [hR]; exact Equiv.Perm.mem_alternatingGroup.mpr hσ
    obtain ⟨g, hg⟩ := hσ'
    have hgK : g ∈ C.V ⊔ K := by rw [hK]; exact Subgroup.mem_top g
    obtain ⟨v, hv, a, ha, hva⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := C.V) (t := K)).mp hgK
    refine ⟨a, ha, ?_⟩
    rw [← hg, ← hva, map_mul, C.rho_eq_one_of_mem hv, one_mul]
  let pick : (K : Subgroup M) → Equiv.Perm (Fin 5) → M := fun K σ =>
    Classical.epsilon (fun a : M => a ∈ K ∧ C.ρ a = σ)
  have pick_spec : ∀ {K : Subgroup M}, C.V ⊔ K = ⊤ →
      ∀ {σ : Equiv.Perm (Fin 5)}, σ.sign = 1 → pick K σ ∈ K ∧ C.ρ (pick K σ) = σ := by
    intro K hK σ hσ
    obtain ⟨a, ha, hρ⟩ := exists_rg K hK hσ
    exact Classical.epsilon_spec (p := fun a : M => a ∈ K ∧ C.ρ a = σ) ⟨a, ha, hρ⟩
  have pick_mul : ∀ {K : Subgroup M}, K ⊓ C.V = ⊥ → C.V ⊔ K = ⊤ →
      ∀ {σ τ : Equiv.Perm (Fin 5)}, σ.sign = 1 → τ.sign = 1 →
        pick K (σ * τ) = pick K σ * pick K τ := by
    intro K hKV hK σ τ hσ hτ
    have hστ : (σ * τ).sign = 1 := by rw [Equiv.Perm.sign_mul, hσ, hτ, mul_one]
    have h1 := pick_spec hK hσ
    have h2 := pick_spec hK hτ
    have h3 := pick_spec hK hστ
    exact eq_of_rho_eq hKV h3.1 (K.mul_mem h1.1 h2.1) (by rw [h3.2, map_mul, h1.2, h2.2])
  have pick_one : ∀ {K : Subgroup M}, K ⊓ C.V = ⊥ → C.V ⊔ K = ⊤ → pick K 1 = 1 := by
    intro K hKV hK
    have h := pick_spec hK one_sign
    exact eq_of_rho_eq hKV h.1 K.one_mem (by rw [h.2, map_one])
  have u_mem : ∀ {D : Subgroup M}, C.V ⊔ D = ⊤ → ∀ {σ : Equiv.Perm (Fin 5)}, σ.sign = 1 →
      pick B σ * (pick D σ)⁻¹ ∈ C.V := by
    intro D hD σ hσ
    have h1 := pick_spec hBL hσ
    have h2 := pick_spec hD hσ
    exact C.mem_of_rho_eq_one (by rw [map_mul, map_inv, h1.2, h2.2, mul_inv_cancel])
  let c : Equiv.Perm (Fin 5) → W5 := fun σ =>
    if h : σ.sign = 1 then C.ψ ⟨pick B σ * (pick A σ)⁻¹, u_mem hAL h⟩ else 1
  have c_eq : ∀ {σ : Equiv.Perm (Fin 5)} (h : σ.sign = 1),
      c σ = C.ψ ⟨pick B σ * (pick A σ)⁻¹, u_mem hAL h⟩ := by
    intro σ h
    simp only [c, dif_pos h]
  have hc1 : c 1 = 1 := by
    rw [c_eq one_sign]
    have e0 : pick B 1 * (pick A 1)⁻¹ = 1 := by
      rw [pick_one hBV hBL, pick_one hAV hAL, inv_one, mul_one]
    have e : (⟨pick B 1 * (pick A 1)⁻¹, u_mem hAL one_sign⟩ : ↥C.V) = 1 :=
      Subtype.ext e0
    rw [e, map_one]
  have hcm : ∀ σ τ : Equiv.Perm (Fin 5), σ.sign = 1 → τ.sign = 1 →
      c (σ * τ) = c σ * pact σ (c τ) := by
    intro σ τ hσ hτ
    have hστ : (σ * τ).sign = 1 := by rw [Equiv.Perm.sign_mul, hσ, hτ, mul_one]
    have haσ : pick A σ ∈ A := (pick_spec hAL hσ).1
    have hρσ : C.ρ (pick A σ) = σ := (pick_spec hAL hσ).2
    have huστ := u_mem hAL hστ
    have huσ := u_mem hAL hσ
    have huτ := u_mem hAL hτ
    have hconjmem : pick A σ * (pick B τ * (pick A τ)⁻¹) * (pick A σ)⁻¹ ∈ C.V :=
      C.hV.conj_mem _ huτ _
    have hconjτ : C.ψ ⟨pick A σ * (pick B τ * (pick A τ)⁻¹) * (pick A σ)⁻¹, hconjmem⟩ =
        pact σ (c τ) := by
      rw [c_eq hτ]
      have h := C.conj_ψ (pick A σ) ⟨pick B τ * (pick A τ)⁻¹, huτ⟩
      rw [hρσ] at h
      exact h
    have hbστ : pick B (σ * τ) = pick B σ * pick B τ := pick_mul hBV hBL hσ hτ
    have haστ : pick A (σ * τ) = pick A σ * pick A τ := pick_mul hAV hAL hσ hτ
    have hX : (⟨pick B (σ * τ) * (pick A (σ * τ))⁻¹, huστ⟩ : ↥C.V) =
        ⟨pick B σ * (pick A σ)⁻¹, huσ⟩ *
          ⟨pick A σ * (pick B τ * (pick A τ)⁻¹) * (pick A σ)⁻¹, hconjmem⟩ :=
      Subtype.ext (by
        show pick B (σ * τ) * (pick A (σ * τ))⁻¹ =
          (pick B σ * (pick A σ)⁻¹) *
            (pick A σ * (pick B τ * (pick A τ)⁻¹) * (pick A σ)⁻¹)
        rw [hbστ, haστ]
        group)
    calc c (σ * τ) = C.ψ ⟨pick B (σ * τ) * (pick A (σ * τ))⁻¹, huστ⟩ := c_eq hστ
      _ = C.ψ (⟨pick B σ * (pick A σ)⁻¹, huσ⟩ *
            ⟨pick A σ * (pick B τ * (pick A τ)⁻¹) * (pick A σ)⁻¹, hconjmem⟩) :=
          congrArg C.ψ hX
      _ = C.ψ ⟨pick B σ * (pick A σ)⁻¹, huσ⟩ *
            C.ψ ⟨pick A σ * (pick B τ * (pick A τ)⁻¹) * (pick A σ)⁻¹, hconjmem⟩ :=
          map_mul _ _ _
      _ = c σ * pact σ (c τ) := by rw [hconjτ, c_eq hσ]
  obtain ⟨v, hv⟩ := cocycle_coboundary_alt c hc1 hcm
  obtain ⟨W, hW⟩ : ∃ W : ↥C.V, C.ψ W = v :=
    ⟨C.ψ.symm v, MulEquiv.apply_symm_apply _ v⟩
  have hWW : W * W = 1 := C.ψ.injective (by rw [map_mul, map_one, hW, sq_W5])
  have hw2 : (W : M) * (W : M) = 1 := congrArg Subtype.val hWW
  have hwinv : (W : M)⁻¹ = (W : M) := inv_eq_of_mul_eq_one_right hw2
  have key : ∀ σ : Equiv.Perm (Fin 5), σ.sign = 1 →
      pick B σ = (W : M)⁻¹ * pick A σ * (W : M) := by
    intro σ hσ
    have haA : pick A σ ∈ A := (pick_spec hAL hσ).1
    have hρ : C.ρ (pick A σ) = σ := (pick_spec hAL hσ).2
    have hYmem : pick A σ * (W : M) * (pick A σ)⁻¹ ∈ C.V := C.hV.conj_mem _ W.2 _
    have hY : C.ψ ⟨pick A σ * (W : M) * (pick A σ)⁻¹, hYmem⟩ = pact σ v := by
      have h := C.conj_ψ (pick A σ) W
      rw [hρ, hW] at h
      exact h
    have huσ := u_mem hAL hσ
    have hcσ : C.ψ ⟨pick B σ * (pick A σ)⁻¹, huσ⟩ = v * pact σ v := by
      rw [← c_eq hσ]
      exact hv σ hσ
    have hmain : W * ⟨pick A σ * (W : M) * (pick A σ)⁻¹, hYmem⟩ =
        ⟨pick B σ * (pick A σ)⁻¹, huσ⟩ :=
      C.ψ.injective (by rw [map_mul, hW, hY, hcσ])
    have hG : (W : M) * (pick A σ * (W : M) * (pick A σ)⁻¹) =
        pick B σ * (pick A σ)⁻¹ := congrArg Subtype.val hmain
    have hpq : pick A σ * (W : M) * (pick A σ)⁻¹ * pick A σ = pick A σ * (W : M) := by
      group
    calc pick B σ = pick B σ * (pick A σ)⁻¹ * pick A σ := by group
      _ = ((W : M) * (pick A σ * (W : M) * (pick A σ)⁻¹)) * pick A σ := by rw [hG]
      _ = (W : M) * (pick A σ * (W : M)) := by rw [mul_assoc, hpq]
      _ = (W : M)⁻¹ * pick A σ * (W : M) := by rw [hwinv, mul_assoc]
  refine ⟨(W : M), W.2, ?_⟩
  intro x
  constructor
  ·
    intro hx
    have hxL : C.ρ x ∈ C.ρ.range := ⟨x, rfl⟩
    rw [hR] at hxL
    have hσ : (C.ρ x).sign = 1 := Equiv.Perm.mem_alternatingGroup.mp hxL
    have hxeq : x = pick B (C.ρ x) :=
      eq_of_rho_eq hBV hx (pick_spec hBL hσ).1 (by rw [(pick_spec hBL hσ).2])
    rw [hxeq, key (C.ρ x) hσ]
    have e : (W : M)⁻¹ * ((W : M)⁻¹ * pick A (C.ρ x) * (W : M)) * (W : M) =
        pick A (C.ρ x) := by
      rw [hwinv]
      calc (W : M) * ((W : M) * pick A (C.ρ x) * (W : M)) * (W : M)
          = ((W : M) * (W : M)) * pick A (C.ρ x) * ((W : M) * (W : M)) := by group
        _ = pick A (C.ρ x) := by rw [hw2, one_mul, mul_one]
    rw [e]
    exact (pick_spec hAL hσ).1
  ·
    intro hx
    obtain ⟨σ, hσdef⟩ : ∃ σ : Equiv.Perm (Fin 5), C.ρ ((W : M)⁻¹ * x * (W : M)) = σ :=
      ⟨_, rfl⟩
    have hyL : C.ρ ((W : M)⁻¹ * x * (W : M)) ∈ C.ρ.range := ⟨_, rfl⟩
    rw [hR] at hyL
    have hσ : σ.sign = 1 := by rw [← hσdef]; exact Equiv.Perm.mem_alternatingGroup.mp hyL
    have hpA : pick A σ ∈ A := (pick_spec hAL hσ).1
    have hyeq : (W : M)⁻¹ * x * (W : M) = pick A σ :=
      eq_of_rho_eq hAV hx hpA (by rw [(pick_spec hAL hσ).2, hσdef])
    have hxa : x = (W : M) * pick A σ * (W : M) := by
      calc x = (W : M) * ((W : M)⁻¹ * x * (W : M)) * (W : M)⁻¹ := by group
        _ = (W : M) * pick A σ * (W : M)⁻¹ := by rw [hyeq]
        _ = (W : M) * pick A σ * (W : M) := by rw [hwinv]
    have hxB : x = pick B σ := by
      rw [key σ hσ, hxa, hwinv]
    rw [hxB]
    exact (pick_spec hBL hσ).1

noncomputable def dsuce_alphaOf (E P : Subgroup G) (hEP : P ≤ Subgroup.normalizer (E : Set G))
    (ψ : ↥E ≃* W5) (m : ↥P) : MulAut W5 :=
  (ψ.symm.trans (conjAct E ⟨(m : G), hEP m.2⟩)).trans ψ

theorem dsuce_alphaOf_psi {E P : Subgroup G} (hEP : P ≤ Subgroup.normalizer (E : Set G))
    (ψ : ↥E ≃* W5) (m : ↥P) (u : ↥E) :
    dsuce_alphaOf E P hEP ψ m (ψ u) = ψ (conjAct E ⟨(m : G), hEP m.2⟩ u) := by
  simp [dsuce_alphaOf]

theorem dsuce_alphaOf_mul {E P : Subgroup G} (hEP : P ≤ Subgroup.normalizer (E : Set G))
    (ψ : ↥E ≃* W5) (m n : ↥P) :
    dsuce_alphaOf E P hEP ψ (m * n) =
      dsuce_alphaOf E P hEP ψ m * dsuce_alphaOf E P hEP ψ n := by
  apply MulEquiv.ext
  intro x
  have hmn : (⟨((m * n : ↥P) : G), hEP (m * n).2⟩ :
      ↥(Subgroup.normalizer (E : Set G))) =
      ⟨(m : G), hEP m.2⟩ * ⟨(n : G), hEP n.2⟩ := Subtype.ext rfl
  simp only [dsuce_alphaOf, MulEquiv.trans_apply, MulAut.mul_apply, hmn, map_mul,
    MulEquiv.symm_apply_apply]

theorem dsuce_alphaOf_one {E P : Subgroup G} (hEP : P ≤ Subgroup.normalizer (E : Set G))
    (ψ : ↥E ≃* W5) : dsuce_alphaOf E P hEP ψ 1 = 1 := by
  apply MulEquiv.ext
  intro x
  have h : (⟨((1 : ↥P) : G), hEP (1 : ↥P).2⟩ :
      ↥(Subgroup.normalizer (E : Set G))) = 1 := Subtype.ext rfl
  simp only [dsuce_alphaOf, MulEquiv.trans_apply, h, map_one, MulAut.one_apply,
    MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]

theorem dsuce_alphaOf_pact {E P L1 : Subgroup G}
    (hEP : P ≤ Subgroup.normalizer (E : Set G)) (ψ : ↥E ≃* W5)
    (α : ↥L1 →* alternatingGroup (Fin 5))
    (hψ : ∀ (ℓ : ↥L1) (u w : ↥E), (w : G) = ℓ * u * ℓ⁻¹ →
      ψ w = pact (α ℓ : Equiv.Perm (Fin 5)) (ψ u))
    (hL1P : L1 ≤ P) (m : ↥P) (ℓ ℓ' : ↥L1)
    (hℓ' : (ℓ' : G) = (m : G) * (ℓ : G) * (m : G)⁻¹) (u : ↥E) :
    dsuce_alphaOf E P hEP ψ m (pact (α ℓ : Equiv.Perm (Fin 5)) (ψ u)) =
      pact (α ℓ' : Equiv.Perm (Fin 5)) (dsuce_alphaOf E P hEP ψ m (ψ u)) := by
  have hℓP : (ℓ : G) ∈ P := hL1P ℓ.2
  have hℓ'P : (ℓ' : G) ∈ P := by
    rw [hℓ']
    exact P.mul_mem (P.mul_mem m.2 hℓP) (P.inv_mem m.2)
  have hmem1 : (ℓ : G) * (u : G) * (ℓ : G)⁻¹ ∈ E :=
    (Subgroup.mem_normalizer_iff.mp (hEP hℓP) (u : G)).mp u.2
  have hmem2 : (ℓ' : G) * ((conjAct E ⟨(m : G), hEP m.2⟩ u : ↥E) : G) *
      (ℓ' : G)⁻¹ ∈ E :=
    (Subgroup.mem_normalizer_iff.mp (hEP hℓ'P) _).mp
      (conjAct E ⟨(m : G), hEP m.2⟩ u).2
  rw [← hψ ℓ u ⟨(ℓ : G) * (u : G) * (ℓ : G)⁻¹, hmem1⟩ rfl]
  rw [show dsuce_alphaOf E P hEP ψ m (ψ ⟨(ℓ : G) * (u : G) * (ℓ : G)⁻¹, hmem1⟩) =
    ψ (conjAct E ⟨(m : G), hEP m.2⟩ ⟨(ℓ : G) * (u : G) * (ℓ : G)⁻¹, hmem1⟩) from
      dsuce_alphaOf_psi hEP ψ m _]
  rw [show dsuce_alphaOf E P hEP ψ m (ψ u) =
    ψ (conjAct E ⟨(m : G), hEP m.2⟩ u) from dsuce_alphaOf_psi hEP ψ m u]
  refine Eq.trans (congrArg ψ (Subtype.ext ?_))
    (hψ ℓ' (conjAct E ⟨(m : G), hEP m.2⟩ u)
      ⟨(ℓ' : G) * ((conjAct E ⟨(m : G), hEP m.2⟩ u : ↥E) : G) * (ℓ' : G)⁻¹, hmem2⟩ rfl)
  show ((conjAct E ⟨(m : G), hEP m.2⟩ ⟨(ℓ : G) * (u : G) * (ℓ : G)⁻¹, hmem1⟩ : ↥E) : G) =
    (ℓ' : G) * ((conjAct E ⟨(m : G), hEP m.2⟩ u : ↥E) : G) * (ℓ' : G)⁻¹
  rw [AutOn.coe_conjAct_apply, AutOn.coe_conjAct_apply, hℓ']
  change (m : G) * ((ℓ : G) * (u : G) * (ℓ : G)⁻¹) * (m : G)⁻¹ =
    ((m : G) * (ℓ : G) * (m : G)⁻¹) * ((m : G) * (u : G) * (m : G)⁻¹) *
      ((m : G) * (ℓ : G) * (m : G)⁻¹)⁻¹
  group

theorem dsuce_alphaOf_exists_pact {E P L1 : Subgroup G}
    (hEP : P ≤ Subgroup.normalizer (E : Set G)) (ψ : ↥E ≃* W5)
    (α : ↥L1 →* alternatingGroup (Fin 5)) (hαs : Function.Surjective α)
    (hψ : ∀ (ℓ : ↥L1) (u w : ↥E), (w : G) = ℓ * u * ℓ⁻¹ →
      ψ w = pact (α ℓ : Equiv.Perm (Fin 5)) (ψ u))
    (hL1P : L1 ≤ P) (hL1N : P ≤ Subgroup.normalizer (L1 : Set G)) (m : ↥P) :
    ∃ π : Equiv.Perm (Fin 5), dsuce_alphaOf E P hEP ψ m = pact π := by
  classical
  have h1 : ∀ σ ∈ alternatingGroup (Fin 5), ∃ τ ∈ alternatingGroup (Fin 5),
      ∀ x : W5, dsuce_alphaOf E P hEP ψ m (pact σ x) =
        pact τ (dsuce_alphaOf E P hEP ψ m x) := by
    intro σ hσ
    obtain ⟨ℓ, hℓ⟩ := hαs ⟨σ, hσ⟩
    have hco : ((α ℓ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) = σ :=
      congrArg Subtype.val hℓ
    rw [← hco]
    have hmem : (m : G) * (ℓ : G) * (m : G)⁻¹ ∈ L1 :=
      (Subgroup.mem_normalizer_iff.mp (hL1N m.2) (ℓ : G)).mp ℓ.2
    refine ⟨α ⟨(m : G) * (ℓ : G) * (m : G)⁻¹, hmem⟩, (α _).2, fun x => ?_⟩
    have h := dsuce_alphaOf_pact hEP ψ α hψ hL1P m ℓ
      ⟨(m : G) * (ℓ : G) * (m : G)⁻¹, hmem⟩ rfl (ψ.symm x)
    simpa using h
  have h2 : ∀ τ ∈ alternatingGroup (Fin 5), ∃ σ ∈ alternatingGroup (Fin 5),
      ∀ x : W5, dsuce_alphaOf E P hEP ψ m (pact σ x) =
        pact τ (dsuce_alphaOf E P hEP ψ m x) := by
    intro τ hτ
    obtain ⟨ℓ', hℓ'⟩ := hαs ⟨τ, hτ⟩
    have hco : ((α ℓ' : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) = τ :=
      congrArg Subtype.val hℓ'
    rw [← hco]
    have hmem : (m : G)⁻¹ * (ℓ' : G) * (m : G) ∈ L1 := by
      have h := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (L1 : Set G)).inv_mem (hL1N m.2)) (ℓ' : G)).mp ℓ'.2
      simpa using h
    refine ⟨α ⟨(m : G)⁻¹ * (ℓ' : G) * (m : G), hmem⟩, (α _).2, fun x => ?_⟩
    have h := dsuce_alphaOf_pact hEP ψ α hψ hL1P m
      ⟨(m : G)⁻¹ * (ℓ' : G) * (m : G), hmem⟩ ℓ' (by simp; group) (ψ.symm x)
    simpa using h
  obtain ⟨π, hπ⟩ := exists_pact_of_normalizes (dsuce_alphaOf E P hEP ψ m) h1 h2
  exact ⟨π, MulEquiv.ext hπ⟩

theorem dsuce_alphaOf_L {E P L1 : Subgroup G}
    (hEP : P ≤ Subgroup.normalizer (E : Set G)) (ψ : ↥E ≃* W5)
    (α : ↥L1 →* alternatingGroup (Fin 5))
    (hψ : ∀ (ℓ : ↥L1) (u w : ↥E), (w : G) = ℓ * u * ℓ⁻¹ →
      ψ w = pact (α ℓ : Equiv.Perm (Fin 5)) (ψ u))
    (hL1P : L1 ≤ P) (ℓ : ↥L1) :
    dsuce_alphaOf E P hEP ψ ⟨(ℓ : G), hL1P ℓ.2⟩ = pact (α ℓ : Equiv.Perm (Fin 5)) := by
  apply MulEquiv.ext
  intro x
  have hmem : (ℓ : G) * ((ψ.symm x : ↥E) : G) * (ℓ : G)⁻¹ ∈ E :=
    (Subgroup.mem_normalizer_iff.mp (hEP (hL1P ℓ.2)) _).mp (ψ.symm x).2
  have h1 := dsuce_alphaOf_psi hEP ψ ⟨(ℓ : G), hL1P ℓ.2⟩ (ψ.symm x)
  rw [MulEquiv.apply_symm_apply] at h1
  rw [h1]
  change ψ ⟨(ℓ : G) * ((ψ.symm x : ↥E) : G) * (ℓ : G)⁻¹, hmem⟩ = pact (α ℓ) x
  rw [hψ ℓ (ψ.symm x) ⟨(ℓ : G) * ((ψ.symm x : ↥E) : G) * (ℓ : G)⁻¹, hmem⟩ rfl,
    MulEquiv.apply_symm_apply]

theorem u42ExtFrame_of_local [Finite G] {L1 L2 S : Subgroup G}
    (h : Hyp111R L1 L2 S) (hS : ¬ S ≤ L1) (hb6 : F112B6Loc L2 L1)
    (hE1 : pCoreOf 2 L1 = dsQ L1 L2 S) (hE16 : Nat.card ↥(pCoreOf 2 L1) = 16)
    (h5 : Nonempty (oTwoQuot ↥(L1 ⊔ bigB L1 L2 S) ≃* Equiv.Perm (Fin 5)))
    (hsylS : IsSylowTwoOf S (L1 ⊔ bigB L1 L2 S)) : U42ExtFrame L1 L2 S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P1 : Subgroup G := L1 ⊔ bigB L1 L2 S with hP1
  set B : Subgroup G := bigB L1 L2 S with hB
  set E : Subgroup G := pCoreOf 2 L1 with hE
  have hE1' : E = pCoreOf 2 P1 := by
    rw [hE, hP1]
    exact hE1
  have hP1card : Nat.card ↥P1 = 1920 := by
    rw [hP1]
    exact dsuce_card_P1 hE1 hE16 h5
  have hL1P : L1 ≤ P1 := by rw [hP1]; exact le_sup_left
  have hP1N : P1 ≤ Subgroup.normalizer (L1 : Set G) := by
    rw [hP1]
    exact CFSG.Quasithin.F1.parabolic_le_normalizer h
  have hEnorm : P1 ≤ Subgroup.normalizer (E : Set G) := by
    rw [hE1']
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P1
  have hE_le_L1 : E ≤ L1 := by rw [hE]; exact CFSG.LieType.BorelTits.pCoreOf_le 2 L1
  have hE_le_P1 : E ≤ P1 := hE_le_L1.trans hL1P
  have hBleP1 : B ≤ P1 := by rw [hP1, hB]; exact le_sup_right
  have hSleB : S ≤ B := by rw [hB]; exact le_sup_right
  have hSleP1 : S ≤ P1 := hSleB.trans hBleP1
  have hb6c : F112B6Loc L2 L1 := hb6
  obtain ⟨-, -, hbl, -, -, halt⟩ := hb6
  have hblk : CFSG.QuasithinUnique.blockU L1 ≤ pCoreOf 2 L1 :=
    hbl.1.2.2.1.1.trans inf_le_left
  obtain ⟨α, ψ, hαs, hαk, hψ⟩ := dsucp_frame_psi halt hblk hE16
  have hψE : ∀ (ℓ : ↥L1) (u w : ↥E), (w : G) = ℓ * u * ℓ⁻¹ →
      ψ w = pact (α ℓ : Equiv.Perm (Fin 5)) (ψ u) := hψ
  let phi : ↥P1 → MulAut W5 := fun m => dsuce_alphaOf E P1 hEnorm ψ m
  have hex : ∀ m : ↥P1, ∃ π : Equiv.Perm (Fin 5), phi m = pact π := fun m =>
    dsuce_alphaOf_exists_pact hEnorm ψ α hαs hψE hL1P hP1N m
  let rho0 : ↥P1 → Equiv.Perm (Fin 5) := fun m => Classical.choose (hex m)
  have rho0_spec : ∀ m : ↥P1, phi m = pact (rho0 m) := fun m =>
    Classical.choose_spec (hex m)
  let rho : ↥P1 →* Equiv.Perm (Fin 5) :=
    { toFun := rho0
      map_one' := by
        apply pact_injective
        rw [map_one, ← rho0_spec 1]
        exact dsuce_alphaOf_one hEnorm ψ
      map_mul' := by
        intro m n
        apply pact_injective
        rw [map_mul, ← rho0_spec (m * n), ← rho0_spec m, ← rho0_spec n]
        exact dsuce_alphaOf_mul hEnorm ψ m n }
  have hrhoL : ∀ ℓ : ↥L1, rho ⟨(ℓ : G), hL1P ℓ.2⟩ = (α ℓ : Equiv.Perm (Fin 5)) := by
    intro ℓ
    apply pact_injective
    change pact (rho0 ⟨(ℓ : G), hL1P ℓ.2⟩) = pact (α ℓ : Equiv.Perm (Fin 5))
    rw [← rho0_spec ⟨(ℓ : G), hL1P ℓ.2⟩]
    exact dsuce_alphaOf_L hEnorm ψ α hψE hL1P ℓ
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    have h' : (⟨a, ha⟩ : ↥E) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
      apply ψ.injective
      rw [map_mul, map_mul, mul_comm]
    exact congrArg Subtype.val h'
  have hrho_one : ∀ m : ↥P1, rho m = 1 ↔ (m : G) ∈ E := by
    intro m
    constructor
    · intro h1
      have hphi : phi m = 1 := by
        rw [rho0_spec m]
        change pact (rho m) = 1
        rw [h1, map_one]
      have hfix : ∀ u : ↥E, conjAct E ⟨(m : G), hEnorm m.2⟩ u = u := by
        intro u
        apply ψ.injective
        have h := congrArg (fun f : MulAut W5 => f (ψ u)) hphi
        rw [MulAut.one_apply] at h
        change dsuce_alphaOf E P1 hEnorm ψ m (ψ u) = ψ u at h
        rw [dsuce_alphaOf_psi] at h
        exact h
      have hcen : (m : G) ∈ Subgroup.centralizer (E : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        have hfixv := hfix ⟨v, hv⟩
        have hcoe := congrArg (fun w : ↥E => (w : G)) hfixv
        rw [AutOn.coe_conjAct_apply] at hcoe
        have hv' : (m : G) * v = v * (m : G) := by
          calc (m : G) * v = ((m : G) * v * (m : G)⁻¹) * (m : G) := by group
            _ = v * (m : G) := by rw [hcoe]
        exact hv'.symm
      have hchar := CFSG.Quasithin.F1.parabolic_charTwo h
      have hmem : (m : G) ∈ P1 ⊓ Subgroup.centralizer (pCoreOf 2 P1 : Set G) := by
        refine ⟨m.2, ?_⟩
        rwa [hE1'] at hcen
      have := hchar hmem
      rwa [← hE1'] at this
    · intro hmE
      apply pact_injective
      change pact (rho0 m) = pact 1
      rw [map_one, ← rho0_spec m]
      apply MulEquiv.ext
      intro x
      have hfix : ∀ u : ↥E, conjAct E ⟨(m : G), hEnorm m.2⟩ u = u := by
        intro u
        apply Subtype.ext
        rw [AutOn.coe_conjAct_apply]
        have hcomm := hEcomm (m : G) hmE (u : G) u.2
        calc (m : G) * (u : G) * (m : G)⁻¹ = (u : G) * (m : G) * (m : G)⁻¹ := by
              rw [hcomm]
          _ = u := by group
      have hx : x = ψ (ψ.symm x) := (MulEquiv.apply_symm_apply ψ x).symm
      calc dsuce_alphaOf E P1 hEnorm ψ m x
          = dsuce_alphaOf E P1 hEnorm ψ m (ψ (ψ.symm x)) := by conv_lhs => rw [hx]
        _ = ψ (conjAct E ⟨(m : G), hEnorm m.2⟩ (ψ.symm x)) :=
            dsuce_alphaOf_psi hEnorm ψ m (ψ.symm x)
        _ = ψ (ψ.symm x) := by rw [hfix (ψ.symm x)]
        _ = x := MulEquiv.apply_symm_apply ψ x
  have hVnorm : (E.subgroupOf P1).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hE_le_P1).mpr hEnorm
  let C : CoordData ↥P1 :=
    { V := E.subgroupOf P1
      hV := hVnorm
      ψ := (Subgroup.subgroupOfEquivOfLe hE_le_P1).trans ψ
      ρ := rho
      ker_ρ := by
        ext m
        rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
        exact hrho_one m
      conj_ψ := by
        intro m v
        have hvE : ((v : ↥P1) : G) ∈ E := Subgroup.mem_subgroupOf.mp v.2
        have h := dsuce_alphaOf_psi hEnorm ψ m ⟨((v : ↥P1) : G), hvE⟩
        change phi m (ψ ⟨((v : ↥P1) : G), hvE⟩) = _ at h
        rw [rho0_spec m] at h
        change ψ ⟨((m * (v : ↥P1) * m⁻¹ : ↥P1) : G),
            (Subgroup.mem_normalizer_iff.mp (hEnorm m.2) ((v : ↥P1) : G)).mp hvE⟩ =
          pact (rho m) (ψ ⟨((v : ↥P1) : G), hvE⟩)
        have heq : (⟨((m * (v : ↥P1) * m⁻¹ : ↥P1) : G),
            (Subgroup.mem_normalizer_iff.mp (hEnorm m.2) ((v : ↥P1) : G)).mp hvE⟩ : ↥E) =
            conjAct E ⟨(m : G), hEnorm m.2⟩ ⟨((v : ↥P1) : G), hvE⟩ :=
          Subtype.ext rfl
        rw [heq]
        exact h.symm }
  have hCV : C.V = E.subgroupOf P1 := rfl
  have hkerC : Nat.card ↥C.V = 16 := by
    rw [hCV]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE_le_P1).toEquiv]
    exact hE16
  have hrangeC : C.ρ.range = ⊤ := by
    have hcard := Subgroup.card_ker_mul_card_range C.ρ
    rw [C.ker_ρ, hkerC, hP1card] at hcard
    have hrange_card : Nat.card ↥C.ρ.range = 120 := by omega
    apply Subgroup.eq_top_of_card_eq
    rw [hrange_card, dsuce_card_perm5]
  have hE_le_Sinf : E ≤ S ⊓ L1 := by
    rw [hE]
    exact CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le h.hyp.h1.sylow
  have hE_le_S : E ≤ S := hE_le_Sinf.trans inf_le_left
  let Ssub : Subgroup ↥P1 := S.subgroupOf P1
  let fS : ↥Ssub →* Equiv.Perm (Fin 5) := C.ρ.comp Ssub.subtype
  have hfS_range : fS.range = Ssub.map C.ρ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hfS_ker : fS.ker = C.V.subgroupOf Ssub := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← C.ker_ρ]
    rfl
  have hCV_le_Ssub : C.V ≤ Ssub := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hE_le_S (by rwa [hCV] at hx)
  have hSsubcard : Nat.card ↥Ssub = 128 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSleP1).toEquiv]
    exact dsuce_card_S hE1 hE16 h5 hsylS
  have hkerSsub : Nat.card ↥(C.V.subgroupOf Ssub) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCV_le_Ssub).toEquiv]
    exact hkerC
  have hcardfS := Subgroup.card_ker_mul_card_range fS
  rw [hfS_ker, hkerSsub, hSsubcard] at hcardfS
  have hrange8 : Nat.card ↥(Ssub.map C.ρ) = 8 := by
    have : Nat.card ↥fS.range = 8 := by omega
    rwa [hfS_range] at this
  have hSsub2 : IsPGroup 2 Ssub :=
    hsylS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSleP1).symm
  have hrhoS2 : IsPGroup 2 (Ssub.map C.ρ) := hSsub2.map C.ρ
  have hrhoSodd : ¬ 2 ∣ (Ssub.map C.ρ).index := by
    have hmul := Subgroup.card_mul_index (Ssub.map C.ρ)
    rw [hrange8, dsuce_card_perm5] at hmul
    have hidx : (Ssub.map C.ρ).index = 15 := by omega
    rw [hidx]
    norm_num
  let PS : Sylow 2 (Equiv.Perm (Fin 5)) := hrhoS2.toSylow hrhoSodd
  obtain ⟨τ, hτ⟩ := MulAction.exists_smul_eq (Equiv.Perm (Fin 5)) PS Dsyl
  have hDmap : (Ssub.map C.ρ).map (MulAut.conj τ).toMonoidHom = Dsub := by
    have hcoe := congrArg (fun Q : Sylow 2 (Equiv.Perm (Fin 5)) =>
      (Q : Subgroup (Equiv.Perm (Fin 5)))) hτ
    rw [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at hcoe
    change MulAut.conj τ • Ssub.map C.ρ = Dsub at hcoe
    rw [Subgroup.pointwise_smul_def] at hcoe
    exact hcoe
  let C' : CoordData ↥P1 := dsuce_relabel C τ
  have hC'V : C'.V = E.subgroupOf P1 := dsuce_relabel_V C τ
  have hC'range : C'.ρ.range = ⊤ := dsuce_relabel_range C τ hrangeC
  have hSmap : Ssub.map C'.ρ = Dsub := by
    rw [dsuce_relabel_map, hDmap]
  have hSiff : ∀ m : ↥P1, (m : G) ∈ S ↔ InD (C'.ρ m) := by
    intro m
    constructor
    · intro hm
      have hmem : C'.ρ m ∈ Ssub.map C'.ρ := ⟨m, Subgroup.mem_subgroupOf.mpr hm, rfl⟩
      rw [hSmap] at hmem
      exact hmem
    · intro hD
      have hmem : C'.ρ m ∈ Ssub.map C'.ρ := by rw [hSmap]; exact hD
      obtain ⟨s, hs, hρs⟩ := hmem
      have h1 : C'.ρ (s⁻¹ * m) = 1 := by rw [map_mul, map_inv, hρs, inv_mul_cancel]
      have h2 : s⁻¹ * m ∈ C'.V := C'.mem_of_rho_eq_one h1
      have h2G : ((s⁻¹ * m : ↥P1) : G) ∈ E := by
        rw [hC'V] at h2
        exact Subgroup.mem_subgroupOf.mp h2
      have h3 : ((s⁻¹ * m : ↥P1) : G) ∈ S := hE_le_S h2G
      have h4 : (s : G) ∈ S := Subgroup.mem_subgroupOf.mp hs
      have hmul : (m : G) = (s : G) * ((s⁻¹ * m : ↥P1) : G) := by simp
      rw [hmul]
      exact S.mul_mem h4 h3
  let T : Subgroup ↥P1 := (S ⊓ L1).subgroupOf P1
  have hCV_le_T : C'.V ≤ T := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    rw [hC'V] at hx
    exact hE_le_Sinf (Subgroup.mem_subgroupOf.mp hx)
  have hTcard : Nat.card ↥T = 64 := by
    change Nat.card ↥((S ⊓ L1).subgroupOf P1) = 64
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := S ⊓ L1) (K := P1)
      (inf_le_left.trans hSleP1)).toEquiv]
    exact dsuce_card_Sinf h hb6c hE16
  let fT : ↥T →* Equiv.Perm (Fin 5) := C'.ρ.comp T.subtype
  have hfT_range : fT.range = T.map C'.ρ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hfT_ker : fT.ker = C'.V.subgroupOf T := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← C'.ker_ρ]
    rfl
  have hkerT : Nat.card ↥(C'.V.subgroupOf T) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCV_le_T).toEquiv]
    rw [hC'V]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE_le_P1).toEquiv]
    exact hE16
  have hcardfT := Subgroup.card_ker_mul_card_range fT
  rw [hfT_ker, hkerT, hTcard] at hcardfT
  have hTmap_card : Nat.card ↥(T.map C'.ρ) = 4 := by
    have : Nat.card ↥fT.range = 4 := by omega
    rwa [hfT_range] at this
  have hTmap_le : T.map C'.ρ ≤ dsuceK4 := by
    rintro _ ⟨x, hx, rfl⟩
    have hxS : (x : G) ∈ S := (Subgroup.mem_subgroupOf.mp hx).1
    have hxD : InD (C'.ρ x) := (hSiff x).mp hxS
    have hxL : (x : G) ∈ L1 := (Subgroup.mem_subgroupOf.mp hx).2
    have hsign : (C'.ρ x).sign = 1 := by
      have hρx : C'.ρ x = τ * rho x * τ⁻¹ := rfl
      have hρx' : rho x = (α ⟨(x : G), hxL⟩ : Equiv.Perm (Fin 5)) := hrhoL ⟨(x : G), hxL⟩
      rw [hρx, hρx', Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv]
      have hα : ((α ⟨(x : G), hxL⟩ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)).sign = 1 :=
        Equiv.Perm.mem_alternatingGroup.mp (α ⟨(x : G), hxL⟩).2
      rw [hα]
      simp
    exact InK4_of_D_alt _ hxD hsign
  have hTmap_eq : T.map C'.ρ = dsuceK4 := by
    apply Subgroup.eq_of_le_of_card_ge hTmap_le
    rw [hTmap_card, dsuce_card_K4]
  have hNiff : ∀ m : ↥P1, m ∈ Subgroup.normalizer (T : Set ↥P1) ↔ (C'.ρ m) 4 = 4 := by
    intro m
    rw [dsuce_normalizer_map_iff C'.ρ C'.ker_ρ hCV_le_T m, hTmap_eq]
    exact dsuce_mem_normalizer_K4_iff (C'.ρ m)
  have hBiff : ∀ m : ↥P1, (m : G) ∈ bigB L1 L2 S ↔ (C'.ρ m) 4 = 4 := by
    intro m
    have hBeq : bigB L1 L2 S = P1 ⊓ Subgroup.normalizer ((S ⊓ L1 : Subgroup G) : Set G) := by
      rw [hP1]
      exact CFSG.Quasithin.F1.bigB_eq_parabolic_inf h
    have hNsub : (Subgroup.normalizer ((S ⊓ L1 : Subgroup G) : Set G)).subgroupOf P1 =
        Subgroup.normalizer (T : Set ↥P1) :=
      Subgroup.subgroupOf_normalizer_eq (H := S ⊓ L1) (N := P1) (inf_le_left.trans hSleP1)
    rw [hBeq, Subgroup.mem_inf]
    constructor
    · intro hm
      have hmN : m ∈ Subgroup.normalizer (T : Set ↥P1) := by
        rw [← hNsub, Subgroup.mem_subgroupOf]
        exact hm.2
      exact (hNiff m).mp hmN
    · intro h4
      refine ⟨m.2, ?_⟩
      have hmN : m ∈ (Subgroup.normalizer ((S ⊓ L1 : Subgroup G) : Set G)).subgroupOf P1 := by
        rw [hNsub]
        exact (hNiff m).mpr h4
      exact Subgroup.mem_subgroupOf.mp hmN
  let TL : Subgroup ↥L1 := (S ⊓ L1).subgroupOf L1
  have hVTL : (pCoreOf 2 L1).subgroupOf L1 ≤ TL := by
    intro y hy
    exact Subgroup.mem_subgroupOf.mpr (hE_le_Sinf (Subgroup.mem_subgroupOf.mp hy))
  have hTL2 : IsPGroup 2 TL :=
    h.hyp.h1.sylow.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  have hTLi : ¬ 2 ∣ TL.index := h.hyp.h1.sylow.2.2
  have hkerα : α.ker ≤ TL := by
    rw [hαk]
    intro y hy
    refine Subgroup.mem_subgroupOf.mpr (hE_le_Sinf ?_)
    rw [hE]
    exact (CFSG.Quasithin.F1.mem_pCore_iff_coe y).mp hy
  have hT0p : IsPGroup 2 (TL.map α) := hTL2.map α
  have hT0i : ¬ 2 ∣ (TL.map α).index := by
    rw [Subgroup.index_map_eq TL hαs hkerα]
    exact hTLi
  obtain ⟨g, hg⟩ := dsucp_sylow_K4 (TL.map α) hT0p hT0i
  let CL : CoordData ↥L1 := dsucp_coords α ψ hαk hψ g
  have hCLrange : CL.ρ.range = alternatingGroup (Fin 5) := dsucp_range α hαs ψ hαk hψ g
  have hρval : ∀ m : ↥L1,
      CL.ρ m = (g : Equiv.Perm (Fin 5)) * ((α m : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) *
        (g : Equiv.Perm (Fin 5))⁻¹ := fun m => rfl
  have hρTL : ∀ t ∈ TL, InK4 (CL.ρ t) := by
    intro t ht
    have h1 : α t ∈ TL.map α := Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
    have h2 := (hg (α t)).mp h1
    rw [hρval]
    have h3 := (CFSG.Quasithin.A5Model.mem_K4).mp h2
    have h4 : ((g : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) *
        ((α t : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) *
        ((g : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))⁻¹ =
        ((g * α t * g⁻¹ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) := by
      simp
    rw [h4]
    exact h3
  have hK4TL : ∀ k : Equiv.Perm (Fin 5), InK4 k → ∃ t ∈ TL, CL.ρ t = k := by
    intro k hk
    have hkA : k ∈ alternatingGroup (Fin 5) :=
      Equiv.Perm.mem_alternatingGroup.mpr (sign_klein k hk)
    have hk'K : (⟨k, hkA⟩ : alternatingGroup (Fin 5)) ∈ CFSG.Quasithin.A5Model.K4 :=
      CFSG.Quasithin.A5Model.mem_K4.mpr hk
    have hx := (hg (g⁻¹ * ⟨k, hkA⟩ * g)).mpr (by
      rw [show g * (g⁻¹ * ⟨k, hkA⟩ * g) * g⁻¹ = ⟨k, hkA⟩ by group]
      exact hk'K)
    obtain ⟨t, ht, hαt⟩ := Subgroup.mem_map.mp hx
    refine ⟨t, ht, ?_⟩
    rw [hρval, hαt]
    show (g : Equiv.Perm (Fin 5)) *
      ((g⁻¹ * ⟨k, hkA⟩ * g : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) *
      (g : Equiv.Perm (Fin 5))⁻¹ = k
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  haveI : CL.V.Normal := CL.hV
  obtain ⟨A0, hA0V, hA0top⟩ := CL.exists_complement_plain TL hVTL hTL2 hTLi hρTL hK4TL
  let A0G : Subgroup G := A0.map L1.subtype
  have hA0G_le : A0G ≤ L1 := Subgroup.map_subtype_le A0
  have hA0G_V : A0G ⊓ E = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxA, hxE⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hxA
    have haV : a ∈ CL.V := Subgroup.mem_subgroupOf.mpr (by rw [← hE]; exact hxE)
    have hbot : a ∈ A0 ⊓ CL.V := ⟨ha, haV⟩
    rw [hA0V] at hbot
    have ha1 : a = 1 := Subgroup.mem_bot.mp hbot
    rw [ha1, map_one]
    exact Subgroup.mem_bot.mpr rfl
  have hE_A0G : E ⊔ A0G = L1 := by
    apply le_antisymm
    · exact sup_le hE_le_L1 hA0G_le
    · intro x hxL
      have hx : (⟨x, hxL⟩ : ↥L1) ∈ CL.V ⊔ A0 := by
        rw [hA0top]
        exact Subgroup.mem_top _
      obtain ⟨v, hv, a, ha, hva⟩ :=
        (Subgroup.mem_sup_of_normal_left (s := CL.V) (t := A0)).mp hx
      have hvG : ((v : ↥L1) : G) ∈ E := by
        rw [hE]
        exact Subgroup.mem_subgroupOf.mp hv
      have haG : ((a : ↥L1) : G) ∈ A0G := Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
      have hxeq : x = ((v : ↥L1) : G) * ((a : ↥L1) : G) := (congrArg Subtype.val hva).symm
      rw [hxeq]
      exact (E ⊔ A0G).mul_mem (Subgroup.mem_sup_left hvG) (Subgroup.mem_sup_right haG)
  have hfixA : ∀ v ∈ E, (∀ a ∈ A0G, v * a = a * v) → v = 1 := by
    intro v hv hcomm
    have hfix : ∀ σ : Equiv.Perm (Fin 5), σ.sign = 1 → pact σ (ψ ⟨v, hv⟩) = ψ ⟨v, hv⟩ := by
      intro σ hσ
      obtain ⟨ℓ, hℓ⟩ := hαs ⟨σ, hσ⟩
      have hℓCL : CL.ρ ℓ = (g : Equiv.Perm (Fin 5)) * σ * (g : Equiv.Perm (Fin 5))⁻¹ := by
        rw [hρval, hℓ]
      have htop : ℓ ∈ CL.V ⊔ A0 := by rw [hA0top]; exact Subgroup.mem_top ℓ
      obtain ⟨v0, hv0, a0, ha0, hva0⟩ :=
        (Subgroup.mem_sup_of_normal_left (s := CL.V) (t := A0)).mp htop
      have hρa : CL.ρ a0 = (g : Equiv.Perm (Fin 5)) * σ * (g : Equiv.Perm (Fin 5))⁻¹ := by
        rw [← hℓCL, ← hva0, map_mul, CL.rho_eq_one_of_mem hv0, one_mul]
      have hαa : α a0 = ⟨σ, hσ⟩ := by
        apply Subtype.ext
        have h := hρa
        rw [hρval] at h
        have h2 := congrArg (fun z => (g : Equiv.Perm (Fin 5))⁻¹ * z * (g : Equiv.Perm (Fin 5))) h
        simpa [mul_assoc] using h2
      have hcommA : (a0 : G) ∈ A0G := Subgroup.mem_map.mpr ⟨a0, ha0, rfl⟩
      have hcv : (a0 : G) * v = v * (a0 : G) := (hcomm _ hcommA).symm
      have hw : (a0 : G) * v * (a0 : G)⁻¹ = v := by
        calc (a0 : G) * v * (a0 : G)⁻¹ = v * (a0 : G) * (a0 : G)⁻¹ := by rw [hcv]
          _ = v := by group
      have hwmem : (a0 : G) * v * (a0 : G)⁻¹ ∈ E :=
        (Subgroup.mem_normalizer_iff.mp (hEnorm (hL1P a0.2)) v).mp hv
      have hψv := hψE a0 ⟨v, hv⟩ ⟨(a0 : G) * v * (a0 : G)⁻¹, hwmem⟩ rfl
      have hwsub : (⟨(a0 : G) * v * (a0 : G)⁻¹, hwmem⟩ : ↥E) = ⟨v, hv⟩ := Subtype.ext hw
      rw [hwsub, hαa] at hψv
      exact hψv.symm
    have h1 : ψ ⟨v, hv⟩ = 1 := dsuce_fix_alt _ hfix
    have h2 : (⟨v, hv⟩ : ↥E) = 1 := ψ.injective (by rw [h1, map_one])
    exact congrArg Subtype.val h2
  have hconj : ∀ g0 ∈ P1, ∃ w ∈ E, ∀ x : G,
      x ∈ A0G ↔ w⁻¹ * (g0 * x * g0⁻¹) * w ∈ A0G := by
    intro g0 hg0
    let ng : ↥(Subgroup.normalizer (L1 : Set G)) := ⟨g0, hP1N hg0⟩
    let B' : Subgroup ↥L1 := A0.map (conjAct L1 ng).toMonoidHom
    have hB'V : B' ⊓ CL.V = ⊥ := by
      rw [eq_bot_iff]
      rintro y ⟨hyB, hyV⟩
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hyB
      have hyE : ((conjAct L1 ng a : ↥L1) : G) ∈ E := by
        rw [hE]
        exact Subgroup.mem_subgroupOf.mp hyV
      have haE : (a : G) ∈ E := by
        have hconj := (Subgroup.mem_normalizer_iff.mp (hEnorm (P1.inv_mem hg0))
          ((conjAct L1 ng a : ↥L1) : G)).mp hyE
        rw [AutOn.coe_conjAct_apply] at hconj
        rw [show ((ng : ↥(Subgroup.normalizer (L1 : Set G))) : G) = g0 from rfl] at hconj
        rw [inv_inv] at hconj
        have h2 : g0⁻¹ * (g0 * (a : G) * g0⁻¹) * g0 = (a : G) := by group
        rwa [h2] at hconj
      have haV : a ∈ CL.V := Subgroup.mem_subgroupOf.mpr (by rw [← hE]; exact haE)
      have hbot : a ∈ A0 ⊓ CL.V := ⟨ha, haV⟩
      rw [hA0V] at hbot
      have ha1 : a = 1 := Subgroup.mem_bot.mp hbot
      simp [ha1]
    have hB'top : CL.V ⊔ B' = ⊤ := by
      rw [eq_top_iff]
      intro y _
      have hyconj : (conjAct L1 ng⁻¹ y : ↥L1) ∈ CL.V ⊔ A0 := by
        rw [hA0top]
        exact Subgroup.mem_top _
      obtain ⟨v, hv, a, ha, hva⟩ :=
        (Subgroup.mem_sup_of_normal_left (s := CL.V) (t := A0)).mp hyconj
      have hvB : conjAct L1 ng v ∈ CL.V := by
        change (((conjAct L1 ng v : ↥L1) : G)) ∈ pCoreOf 2 L1
        rw [← hE]
        have hvE : (v : G) ∈ E := Subgroup.mem_subgroupOf.mp hv
        have h := (Subgroup.mem_normalizer_iff.mp (hEnorm hg0) (v : G)).mp hvE
        rw [AutOn.coe_conjAct_apply]
        rw [show ((ng : ↥(Subgroup.normalizer (L1 : Set G))) : G) = g0 from rfl]
        exact h
      have haB : conjAct L1 ng a ∈ B' := Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
      have hyeq : y = conjAct L1 ng v * conjAct L1 ng a := by
        apply Subtype.ext
        have hvaG := congrArg Subtype.val hva
        rw [Subgroup.coe_mul, AutOn.coe_conjAct_apply] at hvaG
        rw [show ((ng⁻¹ : ↥(Subgroup.normalizer (L1 : Set G))) : G) = g0⁻¹ from rfl] at hvaG
        simp only [inv_inv] at hvaG
        rw [Subgroup.coe_mul, AutOn.coe_conjAct_apply, AutOn.coe_conjAct_apply]
        rw [show ((ng : ↥(Subgroup.normalizer (L1 : Set G))) : G) = g0 from rfl]
        calc (y : G) = g0 * (g0⁻¹ * (y : G) * g0) * g0⁻¹ := by group
          _ = g0 * ((v : G) * (a : G)) * g0⁻¹ := by rw [hvaG]
          _ = (g0 * (v : G) * g0⁻¹) * (g0 * (a : G) * g0⁻¹) := by group
      rw [hyeq]
      exact (CL.V ⊔ B').mul_mem (Subgroup.mem_sup_left hvB) (Subgroup.mem_sup_right haB)
    obtain ⟨w', hw'V, hw'⟩ :=
      dsuce_complement_conj CL hCLrange (A := A0) (B := B') hA0V hA0top hB'V hB'top
    have hwL1 : (w' : G) ∈ L1 := (CFSG.LieType.BorelTits.pCoreOf_le 2 L1) (by
      rw [← hE]
      exact Subgroup.mem_subgroupOf.mp hw'V)
    refine ⟨(w' : G), ?_, fun x => ?_⟩
    · rw [hE]
      exact Subgroup.mem_subgroupOf.mp hw'V
    · constructor
      · intro hx
        obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
        have hyB : conjAct L1 ng a ∈ B' := Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
        have hyA : w'⁻¹ * conjAct L1 ng a * w' ∈ A0 := (hw' _).mp hyB
        refine Subgroup.mem_map.mpr ⟨w'⁻¹ * conjAct L1 ng a * w', hyA, ?_⟩
        show (((w'⁻¹ * conjAct L1 ng a * w' : ↥L1) : G)) =
          (w' : G)⁻¹ * (g0 * (a : G) * g0⁻¹) * (w' : G)
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, AutOn.coe_conjAct_apply]
        rw [show ((ng : ↥(Subgroup.normalizer (L1 : Set G))) : G) = g0 from rfl]
      · intro hx
        obtain ⟨b, hb, hbeq⟩ := Subgroup.mem_map.mp hx
        have hgxg : g0 * x * g0⁻¹ ∈ L1 := by
          have e : g0 * x * g0⁻¹ = (w' : G) * (L1.subtype b) * (w' : G)⁻¹ := by
            rw [hbeq]; group
          rw [e]
          exact L1.mul_mem (L1.mul_mem hwL1 b.2) (L1.inv_mem hwL1)
        have hxL : x ∈ L1 := by
          have e : x = g0⁻¹ * (g0 * x * g0⁻¹) * g0 := by group
          rw [e]
          simpa only [inv_inv] using
            (Subgroup.mem_normalizer_iff.mp (hP1N (P1.inv_mem hg0)) _).mp hgxg
        let y : ↥L1 := conjAct L1 ng ⟨x, hxL⟩
        have hyA : w'⁻¹ * y * w' ∈ A0 := by
          have hyb : w'⁻¹ * y * w' = b := by
            apply Subtype.ext
            change (((w'⁻¹ * conjAct L1 ng ⟨x, hxL⟩ * w' : ↥L1) : G)) = (b : G)
            simp only [Subgroup.coe_mul, Subgroup.coe_inv, AutOn.coe_conjAct_apply]
            rw [show ((ng : ↥(Subgroup.normalizer (L1 : Set G))) : G) = g0 from rfl]
            exact hbeq.symm
          rw [hyb]
          exact hb
        have hyB : y ∈ B' := (hw' y).mpr hyA
        obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp hyB
        have hconjeq : conjAct L1 ng a = y := haeq
        have hxy : a = ⟨x, hxL⟩ := (conjAct L1 ng).injective hconjeq
        exact Subgroup.mem_map.mpr ⟨a, ha, congrArg Subtype.val hxy⟩
  obtain ⟨Csub, hCsubP1, hCsubV, hVE⟩ :=
    CFSG.GH74.QTGen4.U42.exists_complement_of_conj (M := P1) (L := L1) (V := E) (A := A0G)
      hE_le_L1 hL1P (fun g' hg' v hv => (Subgroup.mem_normalizer_iff.mp (hEnorm hg') v).mp hv)
      hA0G_le hA0G_V hconj hfixA
  let A : Subgroup ↥P1 := Csub.subgroupOf P1
  have hAV : A ⊓ C'.V = ⊥ := by
    apply le_antisymm ?_ bot_le
    rintro m ⟨hmA, hmV⟩
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    have hmE : (m : G) ∈ E := by
      rw [hC'V] at hmV
      exact Subgroup.mem_subgroupOf.mp hmV
    have hmC : (m : G) ∈ Csub := Subgroup.mem_subgroupOf.mp hmA
    have hmem : (m : G) ∈ Csub ⊓ E := ⟨hmC, hmE⟩
    rw [hCsubV] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hVA : C'.V ⊔ A = ⊤ := by
    rw [hC'V]
    rw [← Subgroup.subgroupOf_sup hE_le_P1 hCsubP1, hVE, Subgroup.subgroupOf_self]
  refine ⟨C', ?_, hC'range, hSiff, hBiff, ⟨A, hAV, hVA⟩, ?_⟩
  · rw [hC'V, hE]
  · exact dsuce_card_S hE1 hE16 h5 hsylS

end CFSG.Quasithin.F112R.St84
