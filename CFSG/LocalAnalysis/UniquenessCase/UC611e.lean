module

public import CFSG.LocalAnalysis.UniquenessCase.UC611b
public import CFSG.LocalAnalysis.UniquenessCase.UC611c
public import CFSG.LocalAnalysis.UniquenessCase.UC611a
public import CFSG.LocalAnalysis.UniquenessCase.UC611d
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qa
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
public import CFSG.LocalAnalysis.SignalizerFunctor.Coprime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

local notation "W₃" => Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)

theorem uc611_comm_ne_one {P Q : Subgroup G} (e : ↥P ≃* W₃) (hQ2 : IsPGroup 2 Q)
    (hPQ : P ≤ normalizer (Q : Set G)) (hfaith : P ⊓ centralizer (Q : Set G) = ⊥)
    {X : Subgroup G} (hXP : X ≤ P) (hX3 : Nat.card X = 3) (hXA : ¬ X ≤ thompsonSubgroup P) :
    ∃ r ∈ Q ⊓ centralizer (X : Set G), ∃ z ∈ (Subgroup.center ↥P).map P.subtype, z * r ≠ r * z := by
  by_contra hno
  push Not at hno
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hyX, hXy, hy3, hyJ⟩ := uc611_exists_gen_of_card_three hXP hX3 hXA
  have hyP : y ∈ P := hXP hyX
  have hy1 : y ≠ 1 := fun h => hyJ (h ▸ Subgroup.one_mem _)
  obtain ⟨z, hzZ, hz1, hz3, hzcent⟩ := uc611_exists_center_gen e
  have hzP : z ∈ P := by
    obtain ⟨c, -, hc'⟩ := hzZ
    exact hc' ▸ c.2
  have hzJ : z ∈ thompsonSubgroup P := uc22p22q_center_le_thompson P hzZ
  have hzz : zpowers z ≤ thompsonSubgroup P := (Subgroup.zpowers_le).2 hzJ
  have hord : ∀ w : G, w ^ 3 = 1 → w ≠ 1 → orderOf w = 3 := fun w hw3 hw1 => orderOf_eq_prime hw3 hw1
  have hcommyz : ∀ a ∈ zpowers y, ∀ b ∈ zpowers z, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow (show Commute y z from (hzcent y hyP).symm) i j).eq
  have hzpow3 : ∀ (w : G), w ^ 3 = 1 → ∀ a ∈ zpowers w, a ^ 3 = 1 := by
    intro w hw a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw, one_zpow]
  have hgen : ∀ w : G, w ^ 3 = 1 → w ≠ 1 → ∀ a ∈ zpowers w, a ≠ 1 → zpowers a = zpowers w :=
    fun w hw3 hw1 a ha ha1 => uc611_zpowers_eq_of_mem hw3 hw1 ha ha1
  set E : Subgroup G := zpowers y ⊔ zpowers z with hE
  have hEP : E ≤ P := sup_le ((Subgroup.zpowers_le).2 hyP) ((Subgroup.zpowers_le).2 hzP)
  have hinf : zpowers y ⊓ zpowers z = ⊥ := by
    by_contra hne
    obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
    have h1 := hgen y hy3 hy1 w hw.1 hw1'
    have hyw : y ∈ zpowers w := h1 ▸ Subgroup.mem_zpowers y
    exact hyJ ((Subgroup.zpowers_le).2 (hzz hw.2) hyw)
  have hEcard : Nat.card ↥E = 3 ^ 2 := by
    obtain ⟨h1, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (zpowers y) (zpowers z) hcommyz
    rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hord y hy3 hy1,
      hord z hz3 hz1] at h1
    exact h1
  have hEpow : ∀ m : ↥E, m ^ 3 = 1 := by
    intro m
    obtain ⟨a, ha, b, hb, hab⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcommyz m.2
    apply Subtype.ext
    change (m : G) ^ 3 = 1
    rw [← hab, (show Commute a b from hcommyz a ha b hb).mul_pow, hzpow3 y hy3 a ha, hzpow3 z hz3 b hb,
      one_mul]
  have hQ3 : ¬ 3 ∣ Nat.card ↥Q := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hQ2
    rw [hk]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  have hplane := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 3
    Nat.prime_three E Q hEpow hEcard hQ3 (hEP.trans hPQ)
  have hQle : Q ≤ centralizer ({z} : Set G) := by
    refine hplane.le.trans (iSup_le fun m => iSup_le fun hm => ?_)
    obtain ⟨a, ha, b, hb, hab⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcommyz m.2
    have hm1 : (m : G) ≠ 1 := fun h => hm (Subtype.ext h)
    have hm3 : (m : G) ^ 3 = 1 := congrArg Subtype.val (hEpow m)
    intro w hw
    have hwm : (m : G) * w = w * (m : G) := Subgroup.mem_centralizer_iff.1 hw.2 m rfl
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    by_cases ha1 : a = 1
    ·
      have hmb : (m : G) = b := by rw [← hab, ha1, one_mul]
      have hmz : (m : G) ∈ zpowers z := hmb ▸ hb
      have hzm : z ∈ zpowers (m : G) :=
        (hgen z hz3 hz1 m hmz hm1) ▸ Subgroup.mem_zpowers z
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hzm
      rw [← hk]
      exact (Commute.zpow_left (show Commute (m : G) w from hwm) k).eq
    ·
      have hmP : (m : G) ∈ P := hEP m.2
      have hmJ : (m : G) ∉ thompsonSubgroup P := by
        intro hmJ'
        have haJ : a ∈ thompsonSubgroup P := by
          have : a = (m : G) * b⁻¹ := by rw [← hab]; group
          rw [this]
          exact Subgroup.mul_mem _ hmJ' (Subgroup.inv_mem _ (hzz hb))
        have h1 := hgen y hy3 hy1 a ha ha1
        have hya : y ∈ zpowers a := h1 ▸ Subgroup.mem_zpowers y
        exact hyJ ((Subgroup.zpowers_le).2 haJ hya)
      obtain ⟨g, hgP, hconj⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.exists_conj_zpowers_of_not_mem_thompsonSubgroup
        e hyP hy1 hy3 hyJ hmP hm1 hm3 hmJ
      have hu : g * y * g⁻¹ ∈ zpowers (m : G) := by
        rw [hconj, uc22p21c_mem_map_conj]
        simp [mul_assoc]
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hu
      have huw : (g * y * g⁻¹) * w = w * (g * y * g⁻¹) := by
        rw [← hk]
        exact (Commute.zpow_left (show Commute (m : G) w from hwm) k).eq
      have hvQ : g⁻¹ * w * g ∈ Q := by
        have := (mem_normalizer_iff.1 (hPQ ((P.inv_mem hgP))) w).1 hw.1
        simpa using this
      have hvy : y * (g⁻¹ * w * g) = (g⁻¹ * w * g) * y := by
        have h1 := congrArg (fun t => g⁻¹ * t * g) huw
        simp only [mul_assoc, inv_mul_cancel_left] at h1
        simpa [mul_assoc] using h1
      have hvC : g⁻¹ * w * g ∈ centralizer (X : Set G) := by
        refine Subgroup.mem_centralizer_iff.2 fun t ht => ?_
        rw [hXy] at ht
        obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
        exact (Commute.zpow_left (show Commute y (g⁻¹ * w * g) from hvy) l).eq
      have hcv := hno _ ⟨hvQ, hvC⟩ z hzZ
      have hzg := hzcent g hgP
      have hzg' := hzcent g⁻¹ (P.inv_mem hgP)
      calc z * w = z * (g * (g⁻¹ * w * g) * g⁻¹) := by group
        _ = g * (z * (g⁻¹ * w * g)) * g⁻¹ := by
          calc z * (g * (g⁻¹ * w * g) * g⁻¹) = (z * g) * (g⁻¹ * w * g) * g⁻¹ := by group
            _ = (g * z) * (g⁻¹ * w * g) * g⁻¹ := by rw [hzg]
            _ = g * (z * (g⁻¹ * w * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * w * g) * z) * g⁻¹ := by rw [hcv]
        _ = g * (g⁻¹ * w * g) * (z * g⁻¹) := by group
        _ = g * (g⁻¹ * w * g) * (g⁻¹ * z) := by rw [hzg']
        _ = w * z := by group
  have hz : z ∈ P ⊓ centralizer (Q : Set G) := by
    refine ⟨hzP, Subgroup.mem_centralizer_iff.2 fun q hq => ?_⟩
    exact (Subgroup.mem_centralizer_iff.1 (hQle hq) z rfl).symm
  rw [hfaith, Subgroup.mem_bot] at hz
  exact hz1 hz

@[expose] def Cen611 (S : Subgroup G) (k : G) : Prop := ∀ t ∈ S, k * t = t * k

theorem cen611_conj {P S : Subgroup G} (hPS : P ≤ normalizer (S : Set G)) {k : G} (hk : Cen611 S k)
    {g : G} (hg : g ∈ P) : Cen611 S (g * k * g⁻¹) := by
  intro t ht
  have h0 : g⁻¹ * t * g ∈ S := by
    simpa using (mem_normalizer_iff.1 (hPS (P.inv_mem hg)) t).1 ht
  have h1 := hk _ h0
  calc g * k * g⁻¹ * t = g * (k * (g⁻¹ * t * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * t * g) * k) * g⁻¹ := by rw [h1]
    _ = t * (g * k * g⁻¹) := by group

theorem cen611_mul {S : Subgroup G} {k k' : G} (hk : Cen611 S k) (hk' : Cen611 S k') :
    Cen611 S (k * k') := by
  intro t ht
  calc k * k' * t = k * (k' * t) := by group
    _ = k * (t * k') := by rw [hk' t ht]
    _ = (k * t) * k' := by group
    _ = (t * k) * k' := by rw [hk t ht]
    _ = t * (k * k') := by group

theorem cen611_inv {S : Subgroup G} {k : G} (hk : Cen611 S k) : Cen611 S k⁻¹ := by
  intro t ht
  have := hk t ht
  calc k⁻¹ * t = k⁻¹ * (t * k) * k⁻¹ := by group
    _ = k⁻¹ * (k * t) * k⁻¹ := by rw [this]
    _ = t * k⁻¹ := by group

theorem uc611_cen_le_thompson {P S : Subgroup G} (e : ↥P ≃* W₃) (hPS : P ≤ normalizer (S : Set G)) {w : G}
    (hwB : w ∈ (Subgroup.upperCentralSeries ↥P 2).map P.subtype) (hwtriv : ¬ Cen611 S w) :
    ∀ k ∈ P, Cen611 S k → k ∈ thompsonSubgroup P := by
  intro k hkP hk
  by_contra hkJ
  obtain ⟨y', hy'J, hky⟩ := uc611_exists_comm_eq e hkP hkJ hwB
  apply hwtriv
  rw [← hky]
  have h1 : k * y' * k⁻¹ * y'⁻¹ = k * (y' * k⁻¹ * y'⁻¹) := by group
  rw [h1]
  exact cen611_mul hk (cen611_conj hPS (cen611_inv hk) (CFSG.Open.thompsonSubgroup_le_self P hy'J))

theorem uc611_exists_acting {P S : Subgroup G} {x b : G} (hxP : x ∈ P)
    (hb : b ∈ (Subgroup.upperCentralSeries ↥P 2).map P.subtype) (hbs : ¬ Cen611 S b) :
    ∃ w : G, w ∈ (Subgroup.upperCentralSeries ↥P 2).map P.subtype ∧ ¬ Cen611 S w ∧
      Cen611 S (w * x * w⁻¹ * x⁻¹) := by
  by_cases hZ : ∀ z ∈ (Subgroup.center ↥P).map P.subtype, Cen611 S z
  · refine ⟨b, hb, hbs, ?_⟩
    obtain ⟨b', hb'ucs, rfl⟩ := hb
    have h1 := (Subgroup.mem_upperCentralSeries_succ_iff.1 hb'ucs) ⟨x, hxP⟩
    rw [Subgroup.upperCentralSeries_one] at h1
    exact hZ _ ⟨_, h1, rfl⟩
  · push Not at hZ
    obtain ⟨z, hzZ, hzt⟩ := hZ
    refine ⟨z, ?_, hzt, ?_⟩
    · obtain ⟨c, hc, rfl⟩ := hzZ
      refine ⟨c, ?_, rfl⟩
      have : Subgroup.center ↥P ≤ Subgroup.upperCentralSeries ↥P 2 := by
        rw [← Subgroup.upperCentralSeries_one]
        exact Subgroup.upperCentralSeries_mono ↥P (by norm_num)
      exact this hc
    · have hzc : z * x = x * z := by
        obtain ⟨c, hc, rfl⟩ := hzZ
        exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 hc) ⟨x, hxP⟩).symm
      intro t ht
      have h1 : z * x * z⁻¹ * x⁻¹ = 1 := by rw [hzc]; group
      rw [h1]
      simp

theorem uc611_noncyclic_centralizer {P S : Subgroup G} (e : ↥P ≃* W₃) (hSc : IsMulCommutative S)
    (hSp : IsPGroup 2 ↥S) (hPS : P ≤ normalizer (S : Set G)) {x y w : G} (hxP : x ∈ P) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (hxJ : x ∉ thompsonSubgroup P) (hyJ : y ∈ thompsonSubgroup P)
    (hwB : w ∈ (Subgroup.upperCentralSeries ↥P 2).map P.subtype) (hxy : x * y * x⁻¹ * y⁻¹ = w)
    (hwtriv : ¬ Cen611 S w) (hwcomm : Cen611 S (w * x * w⁻¹ * x⁻¹)) :
    ¬ IsCyclic ↥(S ⊓ centralizer ({x} : Set G)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJP : thompsonSubgroup P ≤ P := CFSG.Open.thompsonSubgroup_le_self P
  have hwJ : w ∈ thompsonSubgroup P := uc611_ucs_two_le_thompson e hwB
  have hw3 : w ^ 3 = 1 := uc611_thompson_exp3 e w hwJ
  have hwP : w ∈ P := hJP hwJ
  have hyP : y ∈ P := hJP hyJ
  haveI := hSc
  letI : CommGroup ↥S := IsMulCommutative.instCommGroup
  let α : ↥P →* MulAut ↥S := S.normalizerMonoidHom.comp (Subgroup.inclusion hPS)
  have hα : ∀ (p : ↥P) (t : ↥S), ((α p t : ↥S) : G) = (p : G) * (t : G) * (p : G)⁻¹ := by
    intro p t
    simp [α]
  have hαtriv : ∀ p : ↥P, α p = 1 ↔ Cen611 S (p : G) := by
    intro p
    constructor
    · intro h t ht
      have := congrArg (fun σ : MulAut ↥S => ((σ ⟨t, ht⟩ : ↥S) : G)) h
      simp only [hα] at this
      calc (p : G) * t = (p : G) * t * (p : G)⁻¹ * p := by group
        _ = t * p := by rw [this]; rfl
    · intro h
      ext t
      rw [hα]
      simp [(h _ t.2)]
  let xb : MulAut ↥S := α ⟨x, hxP⟩
  let yb : MulAut ↥S := α ⟨y, hyP⟩
  let wb : MulAut ↥S := α ⟨w, hwP⟩
  have hxb3 : xb ^ 3 = 1 := by
    have h1 : (⟨x, hxP⟩ : ↥P) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [show xb ^ 3 = α ((⟨x, hxP⟩ : ↥P) ^ 3) from (map_pow α _ 3).symm, h1, map_one]
  have hwb3 : wb ^ 3 = 1 := by
    have h1 : (⟨w, hwP⟩ : ↥P) ^ 3 = 1 := Subtype.ext (by simpa using hw3)
    rw [show wb ^ 3 = α ((⟨w, hwP⟩ : ↥P) ^ 3) from (map_pow α _ 3).symm, h1, map_one]
  have hxyb : xb * yb * xb⁻¹ * yb⁻¹ = wb := by
    have h1 : (⟨x, hxP⟩ * ⟨y, hyP⟩ * (⟨x, hxP⟩ : ↥P)⁻¹ * (⟨y, hyP⟩ : ↥P)⁻¹ : ↥P) = ⟨w, hwP⟩ :=
      Subtype.ext (by simpa using hxy)
    have h2 := congrArg α h1
    simpa only [map_mul, map_inv] using h2
  have hwxb : Commute wb xb := by
    have h1 : α ⁅(⟨w, hwP⟩ : ↥P), ⟨x, hxP⟩⁆ = 1 := by
      refine (hαtriv _).2 ?_
      change Cen611 S (w * x * w⁻¹ * x⁻¹)
      exact hwcomm
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_commute.1 h1
  have hwyb : Commute wb yb := by
    have h1 : (⟨w, hwP⟩ : ↥P) * ⟨y, hyP⟩ = ⟨y, hyP⟩ * ⟨w, hwP⟩ := by
      have h0 := congrArg Subtype.val
        ((uc611_thompson_isMulCommutative e).is_comm.comm ⟨w, hwJ⟩ ⟨y, hyJ⟩)
      exact Subtype.ext h0
    change α ⟨w, hwP⟩ * α ⟨y, hyP⟩ = α ⟨y, hyP⟩ * α ⟨w, hwP⟩
    rw [← map_mul, ← map_mul, h1]
  have hwb1 : wb ≠ 1 := fun h => hwtriv ((hαtriv _).1 h)
  have hKJ := uc611_cen_le_thompson e hPS hwB hwtriv
  have hwbind : wb ∉ Subgroup.zpowers xb := by
    rintro ⟨k, hk⟩
    have hk' : xb ^ k = wb := hk
    have h1 : α ((⟨x, hxP⟩ : ↥P) ^ k * (⟨w, hwP⟩ : ↥P)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_zpow]
      change xb ^ k * wb⁻¹ = 1
      rw [hk']
      group
    have h2 : Cen611 S (x ^ k * w⁻¹) := by
      have := (hαtriv _).1 h1
      simpa using this
    have h3 : x ^ k * w⁻¹ ∈ thompsonSubgroup P :=
      hKJ _ (P.mul_mem (P.zpow_mem hxP k) (P.inv_mem hwP)) h2
    have h4 : x ^ k ∈ thompsonSubgroup P := by
      have := (thompsonSubgroup P).mul_mem h3 hwJ
      simpa using this
    by_cases hxk : x ^ k = 1
    · apply hwb1
      rw [← hk']
      have h5 : (⟨x, hxP⟩ : ↥P) ^ k = 1 := Subtype.ext (by simpa using hxk)
      rw [show xb ^ k = α ((⟨x, hxP⟩ : ↥P) ^ k) from (map_zpow α _ k).symm, h5, map_one]
    · have heq := uc611_zpowers_eq_of_mem hx3 hx1 (Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) k) hxk
      have hx' : x ∈ zpowers (x ^ k) := heq ▸ Subgroup.mem_zpowers x
      exact hxJ ((Subgroup.zpowers_le).2 h4 hx')
  have hnc := uc611_l47 hSp xb yb wb hxb3 hwb3 hxyb hwxb hwyb hwb1 hwbind
  intro hcyc
  apply hnc
  let f : ↥((xb : ↥S →* ↥S).eqLocus (MonoidHom.id ↥S)) →* ↥(S ⊓ centralizer ({x} : Set G)) :=
    ((S.subtype.comp ((xb : ↥S →* ↥S).eqLocus (MonoidHom.id ↥S)).subtype).codRestrict
      (S ⊓ centralizer ({x} : Set G)) fun t => by
        refine ⟨t.1.2, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
        rw [Set.mem_singleton_iff] at hh
        subst hh
        have h1 : xb t.1 = t.1 := t.2
        have h2 := congrArg (fun u : ↥S => (u : G)) h1
        simp only [xb, hα] at h2
        calc h * (t.1 : G) = h * t.1 * h⁻¹ * h := by group
          _ = t.1 * h := by rw [h2])
  exact isCyclic_of_injective f (fun a b hab => Subtype.ext (Subtype.ext (congrArg
    (fun u : ↥(S ⊓ centralizer ({x} : Set G)) => (u : G)) hab)))

theorem uc611_B_centralizes {P Q S : Subgroup G} (e : ↥P ≃* W₃) (hQ2 : IsPGroup 2 Q)
    (hPQ : P ≤ normalizer (Q : Set G)) (hSQ : S ≤ Q) (hSc : IsMulCommutative S)
    (hPS : P ≤ normalizer (S : Set G))
    {X : Subgroup G} (hXP : X ≤ P) (hX3 : Nat.card X = 3) (hXA : ¬ X ≤ thompsonSubgroup P)
    {n : ℕ} (hn : rankThreeIsQ8CentralCyclic (Q ⊓ centralizer (X : Set G)) n)
    (hnt : ∃ r ∈ Q ⊓ centralizer (X : Set G), ∃ z ∈ (Subgroup.center ↥P).map P.subtype, z * r ≠ r * z) :
    ∀ b ∈ (Subgroup.upperCentralSeries ↥P 2).map P.subtype, ∀ s ∈ S, b * s = s * b := by
  intro b hb s hs
  by_contra hbs
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hxX, hXx, hx3, hxJ⟩ := uc611_exists_gen_of_card_three hXP hX3 hXA
  have hxP : x ∈ P := hXP hxX
  have hx1 : x ≠ 1 := fun h => hxJ (h ▸ Subgroup.one_mem _)
  obtain ⟨r, hr, z₀, hz₀Z, hrz⟩ := hnt
  have hz₀P : z₀ ∈ P := by
    obtain ⟨c, -, hc'⟩ := hz₀Z
    exact hc' ▸ c.2
  have hz₀cent : ∀ g ∈ P, z₀ * g = g * z₀ := by
    obtain ⟨c, hc, rfl⟩ := hz₀Z
    intro g hg
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 hc) ⟨g, hg⟩).symm
  have hz₀3 : z₀ ^ 3 = 1 := by
    obtain ⟨c, hc, rfl⟩ := hz₀Z
    have h1 := pow_card_eq_one' (x := (⟨c, hc⟩ : ↥(Subgroup.center ↥P)))
    rw [uc611_card_center e] at h1
    exact congrArg (fun w : ↥(Subgroup.center ↥P) => ((w : ↥P) : G)) h1
  obtain ⟨w, hwB, hwtriv, hwcomm⟩ :=
    uc611_exists_acting (S := S) hxP hb (fun h => hbs (h s hs))
  obtain ⟨y, hyJ, hxy⟩ := uc611_exists_comm_eq e hxP hxJ hwB
  have hnc := uc611_noncyclic_centralizer e hSc (hQ2.to_le hSQ) hPS hxP hx3 hx1 hxJ hyJ hwB hxy hwtriv hwcomm
  apply hnc
  have hXC : centralizer (X : Set G) = centralizer ({x} : Set G) := by
    rw [hXx]
    exact uc611_centralizer_zpowers_eq x
  have hTR : S ⊓ centralizer ({x} : Set G) ≤ Q ⊓ centralizer (X : Set G) :=
    le_inf (inf_le_left.trans hSQ) (hXC ▸ inf_le_right)
  haveI hTc : IsMulCommutative ↥(S ⊓ centralizer ({x} : Set G)) := ⟨⟨fun a b => Subtype.ext (by
    have h0 := congrArg Subtype.val (hSc.is_comm.comm ⟨a, a.2.1⟩ ⟨b, b.2.1⟩)
    exact h0)⟩⟩
  have hzT : z₀ ∈ normalizer ((S ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G) := by
    have := uc611_mem_normalizer_inf_centralizer (Q := S) (X := X) hPS hXP hz₀P hz₀cent
    rwa [hXC] at this
  exact uc611_q8cc_cyclic hn hz₀3 (uc611_mem_normalizer_inf_centralizer hPQ hXP hz₀P hz₀cent)
    ⟨r, hr, hrz⟩ hTR hTc hzT

end CFSG.LocalAnalysis.UniquenessCase.UC6
