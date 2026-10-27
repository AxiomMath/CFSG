module

public import CFSG.Quasithin.Vol2.Ch12Sec6L26k
public import CFSG.Quasithin.Vol2.Ch12Sec6L26o

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

namespace S126L211

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H : Subgroup G}

theorem comm_Q_le_U (h : HypF91 T V L V₁ Vp H) (hidx : Vp.relIndex V = 2)
    (hV : ¬ V ≤ pCoreOf 2 H) {K : Subgroup G} (hK : K ∈ cComp H) {v : G} (hv : v ∈ V)
    (hvH : v ∈ H)
    (hKv : modO2Image H K ≤ ⁅modO2Image H K,
      Subgroup.zpowers ((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H)⁆) :
    ∀ q ∈ pCoreOf 2 H, ∀ k ∈ K, q * k * q⁻¹ * k⁻¹ ∈ conjClosure Vp H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := conjClosure Vp H with hU
  set Q := pCoreOf 2 H with hQ
  set C := centralizerMod U H Q with hC
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hQH : Q ≤ H := pCoreOf_le 2 H
  have hUN : H ≤ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure Vp H
  have hQN : H ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 H
  have hCn : ∀ g ∈ H, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
    intro g hg c hc
    obtain ⟨hcH, hcN, hcQ⟩ := hc
    refine ⟨H.mul_mem (H.mul_mem hg hcH) (H.inv_mem hg), hUN (H.mul_mem (H.mul_mem hg hcH)
      (H.inv_mem hg)), fun q hq => ?_⟩
    have hq' : g⁻¹ * q * g ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (hQN (H.inv_mem hg)) q).mp hq
      simpa using this
    have h1 := hcQ _ hq'
    have h2 : g * (c * (g⁻¹ * q * g) * c⁻¹ * (g⁻¹ * q * g)⁻¹) * g⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (hUN hg) _).mp h1
    have e : g * c * g⁻¹ * q * (g * c * g⁻¹)⁻¹ * q⁻¹ =
        g * (c * (g⁻¹ * q * g) * c⁻¹ * (g⁻¹ * q * g)⁻¹) * g⁻¹ := by group
    rw [e]
    exact h2
  have hvC : v ∈ C := by
    refine ⟨hvH, hUN hvH, fun q hq => ?_⟩
    have h1 : q * v * q⁻¹ * v⁻¹ ∈ Vp := (h.F95_2_aux hidx hV).2.2
      (Subgroup.commutator_mem_commutator hq hv)
    have e : v * q * v⁻¹ * q⁻¹ = (q * v * q⁻¹ * v⁻¹)⁻¹ := by group
    rw [e]
    exact (le_conjClosure Vp H) (Vp.inv_mem h1)
  have hvnC : ∀ n : ℤ, v ^ n ∈ C := fun n => C.zpow_mem hvC n
  have hKC : ∀ k ∈ K, ∃ c ∈ C, c⁻¹ * k ∈ Q := by
    intro k hk
    have hmk : ((⟨k, hKH hk⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ modO2Image H K :=
      ⟨⟨k, hKH hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    have hle : ⁅modO2Image H K, Subgroup.zpowers ((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H)⁆ ≤
        (C.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) := by
      rw [Subgroup.commutator_le]
      rintro _ ⟨a, ha, rfl⟩ b hb
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      have haK : (a : G) ∈ K := Subgroup.mem_subgroupOf.mp ha
      refine ⟨⁅a, ⟨v, hvH⟩ ^ n⁆, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
      · rw [commutatorElement_def]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
        exact C.mul_mem (hCn _ a.2 _ (hvnC n)) (C.inv_mem (hvnC n))
      · simp [commutatorElement_def]
    obtain ⟨c, hc, hce⟩ := hle (hKv hmk)
    refine ⟨c, Subgroup.mem_subgroupOf.mp hc, ?_⟩
    have h1 : ((c⁻¹ * ⟨k, hKH hk⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      have : ((c : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) = ((⟨k, hKH hk⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) :=
        hce
      rw [this, inv_mul_cancel]
    exact (S126L26.mk_eq_one_iff _).mp h1
  have hQC : Q ≤ Subgroup.normalizer (C : Set G) := fun q hq => by
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨fun hc => hCn q (hQH hq) c hc, fun hc => ?_⟩
    have := hCn q⁻¹ (H.inv_mem (hQH hq)) _ hc
    simpa [mul_assoc] using this
  have hKX : K ≤ C ⊔ Q := by
    intro k hk
    obtain ⟨c, hc, hcq⟩ := hKC k hk
    have e : k = c * (c⁻¹ * k) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hc hcq
  have hpow : ∀ x ∈ C ⊔ Q, ∃ m : ℕ, x ^ 2 ^ m ∈ C := fun x hx =>
    S126L24.exists_pow_mem_of_mem_sup hQC (pCoreOf_isPGroup 2 H) hx
  have hKperf : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hK)
  have hKC' : K ≤ C := (CFSG.Quasithin.perfect_le_oTwoUpper hKX hKperf).trans
    (oTwoUpper_le_of_pow_mem hpow)
  intro q hq k hk
  have h1 := (hKC' hk).2.2 q hq
  have e : q * k * q⁻¹ * k⁻¹ = (k * q * k⁻¹ * q⁻¹)⁻¹ := by group
  rw [e]
  exact U.inv_mem h1

theorem mem_of_mk_mem {K : Subgroup G} (hK : K ∈ cComp H) {p : G} (hpH : p ∈ H)
    (hp3 : p ^ 3 = 1)
    (hpK : ((⟨p, hpH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ modO2Image H K) : p ∈ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hQH : pCoreOf 2 H ≤ H := pCoreOf_le 2 H
  have hsolv : Group.IsSolvable ↥(pCoreOf 2 H) := by
    have := (pCoreOf_isPGroup 2 H).isNilpotent
    infer_instance
  have hKQ : ⁅K, pCoreOf 2 H⁆ ≤ K := (cComp_commutator_perfectCore hK hQH hsolv
    (hKH.trans (le_normalizer_pCoreOf 2 H))).1
  have hQK : pCoreOf 2 H ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mpr hKQ
  obtain ⟨k, hk, hke⟩ := hpK
  have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
  have hq : (k : G)⁻¹ * p ∈ pCoreOf 2 H := by
    have h1 : ((k⁻¹ * ⟨p, hpH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      have : ((k : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) = ((⟨p, hpH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) := hke
      rw [this, inv_mul_cancel]
    exact (S126L26.mk_eq_one_iff _).mp h1
  have hpX : p ∈ K ⊔ pCoreOf 2 H := by
    have e : p = (k : G) * ((k : G)⁻¹ * p) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hkK hq
  obtain ⟨m, hm⟩ := S126L24.exists_pow_mem_of_mem_sup hQK (pCoreOf_isPGroup 2 H) hpX
  have ho : orderOf p ∣ 3 := orderOf_dvd_of_pow_eq_one hp3
  have hcop : Nat.Coprime (2 ^ m) (orderOf p) :=
    Nat.Coprime.coprime_dvd_right ho (Nat.Coprime.pow_left m (by norm_num))
  exact (Subgroup.zpowers_le.mpr hm) (A4.mem_zpowers_pow_of_coprime hcop)

omit [Finite G] in
theorem comm_le_Q {R : Subgroup G} (hRH : R ≤ H) {p : G} (hpH : p ∈ H)
    (hcomm : ⁅(R.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)),
      Subgroup.zpowers ((⟨p, hpH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H)⁆ = ⊥) :
    ⁅R, Subgroup.zpowers p⁆ ≤ pCoreOf 2 H := by
  rw [Subgroup.commutator_le]
  intro r hr x hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hrH := hRH hr
  have hpn : p ^ n ∈ H := H.zpow_mem hpH n
  have h1 : ⁅((⟨r, hrH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H),
      ((⟨p, hpH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) ^ n⁆ ∈ (⊥ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    rw [← hcomm]
    exact Subgroup.commutator_mem_commutator ⟨⟨r, hrH⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩
      (Subgroup.zpow_mem_zpowers _ n)
  rw [Subgroup.mem_bot] at h1
  have e : ⁅((⟨r, hrH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H),
      ((⟨p, hpH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) ^ n⁆ =
      ((⁅(⟨r, hrH⟩ : ↥H), (⟨p, hpH⟩ : ↥H) ^ n⁆ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) := by
    simp [commutatorElement_def]
  rw [e] at h1
  have h2 := (S126L26.mk_eq_one_iff _).mp h1
  simpa [commutatorElement_def] using h2

theorem comm_le_comm_U {R K : Subgroup G} (hR2 : IsPGroup 2 R) {p : G}
    (hpR : p ∈ Subgroup.normalizer (R : Set G)) (hp3 : p ^ 3 = 1) (hpK : p ∈ K)
    (hRQ : ⁅R, Subgroup.zpowers p⁆ ≤ pCoreOf 2 H)
    (hQK : ∀ q ∈ pCoreOf 2 H, ∀ k ∈ K, q * k * q⁻¹ * k⁻¹ ∈ conjClosure Vp H) :
    ⁅R, Subgroup.zpowers p⁆ ≤ ⁅conjClosure Vp H, Subgroup.zpowers p⁆ := by
  have hXN : Subgroup.zpowers p ≤ Subgroup.normalizer (R : Set G) := Subgroup.zpowers_le.mpr hpR
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers p)) (Nat.card R) := by
    obtain ⟨n, hn⟩ := hR2.exists_card_eq
    rw [hn, Nat.card_zpowers]
    exact Nat.Coprime.pow_right n (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hp3)
      (by norm_num))
  have hidem := S126Cop.comm_comm_eq hXN hcop
  have hU : ⁅R, Subgroup.zpowers p⁆ ≤ conjClosure Vp H := by
    rw [← hidem, Subgroup.commutator_le]
    intro q hq x hx
    exact hQK q (hRQ hq) x ((Subgroup.zpowers_le.mpr hpK) hx)
  rw [← hidem]
  exact Subgroup.commutator_mono hU le_rfl

omit [Finite G] in
theorem card_sup_le_mul {X Y : Subgroup G} (hXY : X ≤ Subgroup.normalizer (Y : Set G)) :
    Nat.card ↥(X ⊔ Y) ≤ Nat.card X * Nat.card Y := by
  have h := Subgroup.coe_mul_of_left_le_normalizer_right X Y hXY
  calc Nat.card ↥(X ⊔ Y) = Nat.card ((X : Set G) * (Y : Set G)) := by
        rw [← h]; rfl
    _ ≤ Nat.card (X : Set G) * Nat.card (Y : Set G) := Set.natCard_mul_le
    _ = Nat.card X * Nat.card Y := rfl

theorem card_comm_U_le (h : HypF91 T V L V₁ Vp H) (hidx : Vp.relIndex V = 2)
    (hV : ¬ V ≤ pCoreOf 2 H) (hcard : Nat.card Vp = 32) {v : G} (hv : v ∈ V) {p g : G}
    (hpH : p ∈ H) (hp3 : p ^ 3 = 1) (hgH : g ∈ H)
    (hinv : (g * v * g⁻¹) * p * (g * v * g⁻¹)⁻¹ * p ∈ pCoreOf 2 H) :
    Nat.card ↥⁅conjClosure Vp H, Subgroup.zpowers p⁆ ≤ 2 ^ 9 := by
  classical
  set U := conjClosure Vp H with hU
  set Q := pCoreOf 2 H with hQ
  have hUH : U ≤ H := h.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  have hvH : v ∈ H := h.V_le_H hv
  have hv2 : v * v = 1 := by
    rw [← sq]
    exact isElemAbelian_pow_eq_one h.elemAbelian hv
  set a := g * v * g⁻¹ with ha
  have haH : a ∈ H := H.mul_mem (H.mul_mem hgH hvH) (H.inv_mem hgH)
  set b := p * a * p⁻¹ with hb
  have hbH : b ∈ H := H.mul_mem (H.mul_mem hpH haH) (H.inv_mem hpH)
  have hq : (a * b)⁻¹ * p ∈ Q := by
    set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
    set A := π ⟨a, haH⟩ with hA
    set X := π ⟨p, hpH⟩ with hX
    have hpa : a * p * a⁻¹ * p ∈ H := H.mul_mem (H.mul_mem (H.mul_mem haH hpH) (H.inv_mem haH)) hpH
    have h1 : A * X * A⁻¹ * X = 1 := by
      have := (S126L26.mk_eq_one_iff (⟨a * p * a⁻¹ * p, hpa⟩ : ↥H)).mpr hinv
      rw [hA, hX, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact this
    have h2 : A * A = 1 := by
      have ha2 : a * a = 1 := by
        rw [ha]
        calc g * v * g⁻¹ * (g * v * g⁻¹) = g * (v * v) * g⁻¹ := by group
          _ = 1 := by rw [hv2]; group
      rw [hA, ← map_mul]
      have : (⟨a, haH⟩ : ↥H) * ⟨a, haH⟩ = 1 := Subtype.ext ha2
      rw [this, map_one]
    have h3 : X ^ 3 = 1 := by
      rw [hX, ← map_pow]
      have : (⟨p, hpH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hp3)
      rw [this, map_one]
    have hAi : A⁻¹ = A := inv_eq_of_mul_eq_one_right h2
    rw [hAi] at h1
    have h4 : A * X * A = X⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h5 : A * X⁻¹ * A = X := by
      have := congrArg (·⁻¹) h4
      simp only [mul_inv_rev, inv_inv, hAi, mul_assoc] at this
      rw [mul_assoc]
      exact this
    have hab : (a * b)⁻¹ * p ∈ H := H.mul_mem (H.inv_mem (H.mul_mem haH hbH)) hpH
    apply (S126L26.mk_eq_one_iff (⟨(a * b)⁻¹ * p, hab⟩ : ↥H)).mp
    have e : (⟨(a * b)⁻¹ * p, hab⟩ : ↥H) =
        (⟨p, hpH⟩ : ↥H) * (⟨a, haH⟩ : ↥H)⁻¹ * (⟨p, hpH⟩ : ↥H)⁻¹ * (⟨a, haH⟩ : ↥H)⁻¹ *
          (⟨p, hpH⟩ : ↥H) := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hb]
      group
    change π _ = 1
    rw [e]
    simp only [map_mul, map_inv]
    rw [← hA, ← hX, hAi]
    calc X * A * X⁻¹ * A * X = X * (A * X⁻¹ * A) * X := by group
      _ = X * X * X := by rw [h5]
      _ = X ^ 3 := by rw [pow_succ, sq]
      _ = 1 := h3
  have hUN : H ≤ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure Vp H
  have hapg : a * p * g ∈ H := H.mul_mem (H.mul_mem haH hpH) hgH
  set A₅ := Vp.map (MulAut.conj g).toMonoidHom with hA₅
  set B₅ := Vp.map (MulAut.conj (a * p * g)).toMonoidHom with hB₅
  have hmemA : ∀ x ∈ Vp, g * x * g⁻¹ ∈ A₅ := fun x hx => ⟨x, hx, rfl⟩
  have hmemB : ∀ x ∈ Vp, (a * p * g) * x * (a * p * g)⁻¹ ∈ B₅ := fun x hx => ⟨x, hx, rfl⟩
  have hconjU : ∀ {k : G}, k ∈ H → Vp.map (MulAut.conj k).toMonoidHom ≤ U := by
    intro k hk
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hUN hk) x).mp (le_conjClosure Vp H hx)
  have hAU : A₅ ≤ U := hconjU hgH
  have hBU : B₅ ≤ U := hconjU hapg
  have hV₁conj : ∀ {k : G}, k ∈ H → V₁ ≤ Vp.map (MulAut.conj k).toMonoidHom := by
    intro k hk z hz
    refine ⟨k⁻¹ * z * k, h.V₁_le_Vp ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    have := (Subgroup.mem_normalizer_iff.mp (h.H_normalizes_V₁ (H.inv_mem hk)) z).mp hz
    simpa using this
  have hV₁B : V₁ ≤ B₅ := hV₁conj hapg
  have hcardconj : ∀ k : G, Nat.card ↥(Vp.map (MulAut.conj k).toMonoidHom) = 32 := fun k => by
    rw [Subgroup.card_map_of_injective (MulEquiv.injective _), hcard]
  have hUV : ⁅U, V⁆ ≤ Vp := (h.F95_2_aux hidx hV).2.1
  have hcomm1 : ∀ u ∈ U, ⁅u, p⁆ ∈ A₅ ⊔ B₅ := by
    intro u hu
    have huH := hUH hu
    have hq' : (a * b)⁻¹ * p ∈ Q := hq
    set q := (a * b)⁻¹ * p with hqdef
    have hp : p = a * b * q := by rw [hqdef]; group
    have e : ⁅u, p⁆ = ⁅u, a⁆ * (a * ⁅u, b⁆ * a⁻¹) * ((a * b) * ⁅u, q⁆ * (a * b)⁻¹) := by
      rw [hp]
      simp only [commutatorElement_def]
      group
    rw [e]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_)
      (Subgroup.mem_sup_right ?_)) (Subgroup.mem_sup_right (hV₁B ?_))
    ·
      have hu' : g⁻¹ * u * g ∈ U := by
        have := (Subgroup.mem_normalizer_iff.mp (hUN (H.inv_mem hgH)) u).mp hu
        simpa using this
      have h1 := hUV (Subgroup.commutator_mem_commutator hu' hv)
      have e1 : ⁅u, a⁆ = g * ⁅g⁻¹ * u * g, v⁆ * g⁻¹ := by
        rw [ha]
        simp only [commutatorElement_def]
        group
      rw [e1]
      exact hmemA _ h1
    ·
      have hpg : p * g ∈ H := H.mul_mem hpH hgH
      have hu' : (p * g)⁻¹ * u * (p * g) ∈ U := by
        have := (Subgroup.mem_normalizer_iff.mp (hUN (H.inv_mem hpg)) u).mp hu
        simpa using this
      have h1 := hUV (Subgroup.commutator_mem_commutator hu' hv)
      have e1 : a * ⁅u, b⁆ * a⁻¹ = (a * p * g) * ⁅(p * g)⁻¹ * u * (p * g), v⁆ * (a * p * g)⁻¹ := by
        rw [hb, ha]
        simp only [commutatorElement_def]
        group
      rw [e1]
      exact hmemB _ h1
    ·
      have h1 : ⁅u, q⁆ ∈ V₁ := by
        rw [commutatorElement_def]
        exact h.commutator_conjClosure_le u hu q hq'
      exact (Subgroup.mem_normalizer_iff.mp (h.H_normalizes_V₁ (H.mul_mem haH hbH)) _).mp h1
  have hcommn : ∀ n : ℕ, ∀ u ∈ U, ⁅u, p ^ n⁆ ∈ A₅ ⊔ B₅ := by
    intro n
    induction n with
    | zero => intro u _; simp
    | succ n ih =>
      intro u hu
      have hpn : p ^ n ∈ H := H.pow_mem hpH n
      have hu' : p ^ n * u * (p ^ n)⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hUN hpn) u).mp hu
      have e : ⁅u, p ^ (n + 1)⁆ = ⁅u, p ^ n⁆ * ⁅p ^ n * u * (p ^ n)⁻¹, p⁆ := by
        simp only [commutatorElement_def, pow_succ]
        group
      rw [e]
      exact Subgroup.mul_mem _ (ih u hu) (hcomm1 _ hu')
  have hle : ⁅U, Subgroup.zpowers p⁆ ≤ A₅ ⊔ B₅ := by
    rw [Subgroup.commutator_le]
    intro u hu x hx
    rw [← mem_powers_iff_mem_zpowers] at hx
    obtain ⟨n, rfl⟩ := hx
    exact hcommn n u hu
  have hN₁ : U ≤ Subgroup.normalizer (V₁ : Set G) := hUH.trans h.H_normalizes_V₁
  have hAN : A₅ ≤ Subgroup.normalizer (V₁ : Set G) := hAU.trans hN₁
  have hBN : B₅ ≤ Subgroup.normalizer (V₁ : Set G) := hBU.trans hN₁
  have hsupN : A₅ ⊔ B₅ ≤ Subgroup.normalizer (V₁ : Set G) := sup_le hAN hBN
  have h1 := S126L26.card_tildeOf_mul h.card_V₁ (hV₁B.trans le_sup_right) hsupN
  have hAc : Nat.card ↥(tildeOf V₁ A₅) * 2 = Nat.card A₅ :=
    S126L26.card_tildeOf_mul h.card_V₁ (hV₁conj hgH) hAN
  have hBc : Nat.card ↥(tildeOf V₁ B₅) * 2 = Nat.card B₅ :=
    S126L26.card_tildeOf_mul h.card_V₁ hV₁B hBN
  have hA32 : Nat.card A₅ = 32 := hcardconj g
  have hB32 : Nat.card B₅ = 32 := hcardconj (a * p * g)
  rw [hA32] at hAc
  rw [hB32] at hBc
  rw [tildeOf_sup hAN hBN] at h1
  have hWe := h.isElemAbelian_tilde
  have hAt : tildeOf V₁ A₅ ≤ tildeOf V₁ U := secImg_mono hAU
  have hBt : tildeOf V₁ B₅ ≤ tildeOf V₁ U := secImg_mono hBU
  have hcommt : tildeOf V₁ A₅ ≤ Subgroup.normalizer ((tildeOf V₁ B₅ : Subgroup _) : Set _) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hxy : ∀ y ∈ tildeOf V₁ U, x * y * x⁻¹ = y := by
      intro y hy
      have := hWe.1.is_comm.comm ⟨x, hAt hx⟩ ⟨y, hy⟩
      have e : x * y = y * x := congrArg Subtype.val this
      rw [e]
      group
    constructor
    · intro hy
      rw [hxy y (hBt hy)]
      exact hy
    · intro hy
      have hyU : y ∈ tildeOf V₁ U := by
        have h2 := hBt hy
        have h3 : x⁻¹ * (x * y * x⁻¹) * x = y := by group
        rw [← h3]
        exact (tildeOf V₁ U).mul_mem ((tildeOf V₁ U).mul_mem
          ((tildeOf V₁ U).inv_mem (hAt hx)) h2) (hAt hx)
      rw [← hxy y hyU]
      exact hy
  have h2 := card_sup_le_mul hcommt
  have hA16 : Nat.card ↥(tildeOf V₁ A₅) = 16 := by omega
  have hB16 : Nat.card ↥(tildeOf V₁ B₅) = 16 := by omega
  rw [hA16, hB16] at h2
  calc Nat.card ↥⁅U, Subgroup.zpowers p⁆ ≤ Nat.card ↥(A₅ ⊔ B₅) := Subgroup.card_le_of_le hle
    _ ≤ 2 ^ 9 := by omega

end S126L211

end CFSG.Quasithin.H13
