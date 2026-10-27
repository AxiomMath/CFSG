module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45RestTorus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGRawTorusP (p : ℕ) : LargeEvenRawCont :=
  fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
    ∀ f ∈ F, orderOf f = p → ∀ u ∈ I, ∀ E : Subgroup (MulAut R), IsElemAbelian p E →
      (∀ e ∈ E, e ∈ I) → (∀ e ∈ E, e * (u * f * u⁻¹) = u * f * u⁻¹ * e) →
      (∀ r : R, MulAut.conj r ^ p = 1 → (∀ e ∈ E, MulAut.conj r * e = e * MulAut.conj r) →
        MulAut.conj r * (u * f * u⁻¹) = u * f * u⁻¹ * MulAut.conj r → MulAut.conj r ∈ E) →
      ∃ n : ℕ, ∀ s ∈ I, ∀ t ∈ I, (∃ k : ℕ, s ^ p ^ k = 1) → (∃ k : ℕ, t ^ p ^ k = 1) →
        (∀ e ∈ E, s * e = e * s) → (∀ e ∈ E, t * e = e * t) →
        s * t = t * s ∧ u * f * u⁻¹ * s * (u * f * u⁻¹)⁻¹ = s ^ n

@[expose] def GGRawTorusPInput : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    LargeEvenLabelAll lab (GGRawTorusP p)

section Lift

variable {G : Type*} [Group G] (K : Subgroup G) {R : Type} [Group R]
  (θ : K ⧸ Subgroup.center K ≃* R)

theorem ggLAut_mk_self (k : K) :
    ggLAut K θ ⟨k, Subgroup.le_normalizer k.2⟩ =
      MulAut.conj (θ (k : K ⧸ Subgroup.center K)) := by
  ext r
  obtain ⟨q, rfl⟩ := θ.surjective r
  induction q using QuotientGroup.induction_on with
  | H l =>
    have h : (K.normalizerMonoidHom ⟨(k : G), Subgroup.le_normalizer k.2⟩ l : K) =
        k * l * k⁻¹ := Subtype.ext (by rw [normalizerMonoidHom_coe]; simp)
    rw [ggLAut_apply, h, MulAut.conj_apply]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv]

variable {K θ}

theorem orderOf_dvd_card_center [Finite G] {c : G} (hcK : c ∈ K)
    (hcC : c ∈ Subgroup.centralizer (K : Set G)) :
    orderOf c ∣ Nat.card (Subgroup.center K) := by
  have hcZ : (⟨c, hcK⟩ : K) ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro z
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hcC z z.2)
  have h := orderOf_dvd_natCard (⟨⟨c, hcK⟩, hcZ⟩ : Subgroup.center K)
  rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe] at h
  exact h

theorem commute_of_ggLAut_commute [Finite G] (hK : commutator K = ⊤) {p : ℕ}
    (hZ : Nat.Coprime p (Nat.card (Subgroup.center K))) {k g : G} (hk : k ∈ K) (hkp : k ^ p = 1)
    (hg : g ∈ Subgroup.normalizer (K : Set G))
    (hc : ggLAut K θ ⟨g, hg⟩ * ggLAut K θ ⟨k, Subgroup.le_normalizer hk⟩ =
      ggLAut K θ ⟨k, Subgroup.le_normalizer hk⟩ * ggLAut K θ ⟨g, hg⟩) :
    g * k = k * g := by
  set c : G := g * k * g⁻¹ * k⁻¹ with hcdef
  have hcN : c ∈ Subgroup.normalizer (K : Set G) :=
    mul_mem (mul_mem (mul_mem hg (Subgroup.le_normalizer hk)) (inv_mem hg))
      (inv_mem (Subgroup.le_normalizer hk))
  have hc1 : ggLAut K θ ⟨c, hcN⟩ = 1 := by
    have e : (⟨c, hcN⟩ : Subgroup.normalizer (K : Set G)) =
        ⟨g, hg⟩ * ⟨k, Subgroup.le_normalizer hk⟩ * (⟨g, hg⟩ : Subgroup.normalizer (K : Set G))⁻¹ *
          (⟨k, Subgroup.le_normalizer hk⟩ : Subgroup.normalizer (K : Set G))⁻¹ := Subtype.ext rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  have hcC : c ∈ Subgroup.centralizer (K : Set G) := mem_centralizer_of_ggLAut_eq_one K θ hK hc1
  have hcK : c ∈ K := by
    have h1 : g * k * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hg k).mp hk
    exact mul_mem h1 (inv_mem hk)
  have hck : Commute c k := (Subgroup.mem_centralizer_iff.mp hcC k hk).symm
  have hcp : c ^ p = 1 := by
    have h1 : (g * k * g⁻¹) ^ p = 1 := by rw [conj_pow, hkp]; group
    have h2 : g * k * g⁻¹ = c * k := by rw [hcdef]; group
    rw [h2, hck.mul_pow, hkp, mul_one] at h1
    exact h1
  have hord : orderOf c = 1 :=
    Nat.eq_one_of_dvd_coprimes hZ (orderOf_dvd_of_pow_eq_one hcp)
      (orderOf_dvd_card_center hcK hcC)
  have hc1' : c = 1 := orderOf_eq_one_iff.mp hord
  calc g * k = c * (k * g) := by rw [hcdef]; group
    _ = k * g := by rw [hc1', one_mul]

end Lift

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}

theorem pow_eq_self_of_mod_eq_one {M : Type*} [Monoid M] {a : M} {p m : ℕ} (ha : a ^ p = 1)
    (hm : m % p = 1) : a ^ m = a := by
  rw [← Nat.div_add_mod m p, hm, pow_add, pow_mul, ha, one_pow, one_mul, pow_one]

theorem GGL45Config.torusAbPow_of_coprime (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) (hT : GGRawTorusPInput)
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁)
    (hZ : Nat.Coprime p (Nat.card (Subgroup.center K))) :
    (∀ a ∈ U₁, ∀ b ∈ U₁, a * b * a⁻¹ * b⁻¹ ∈ U ⊓ Subgroup.centralizer (K : Set G)) ∧
      ∃ e : ℕ, ∀ u ∈ U₁, (u ^ e)⁻¹ * (x⁻¹ * u * x) ∈ U ⊓ Subgroup.centralizer (K : Set G) := by
  have hp : p.Prime := hcfg.prime
  have hp2 : p ≠ 2 := hcfg.odd
  have hUK := hcfg.le_normalizer
  have hBsU := hcfg.bs_le
  have hKp : commutator K = ⊤ := hcfg.2.2.2.2.2.2.2.1.2.2.1
  obtain ⟨hB₁U₁, hxU₁, -⟩ := ggL4546_basic hraw hiso hcfg
  obtain ⟨R, _, I, F, θ, hs, hna, hRIF, hTP, hB₁I, ⟨f, hf, u, hu, hord, hxind⟩, hiff⟩ :=
    ggL4546_exists_marking (P' := GGRawTorusP p) (fun lab hl => hT p hp hp2 lab hl) hraw hiso
      hcfg
  obtain ⟨-, -, hinn, -⟩ := hRIF hs hna
  have hxU : x ∈ U := hBsU hcfg.x_mem
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := hUK hxU
  have hψ : u * f * u⁻¹ = ggLAut K θ ⟨x⁻¹, inv_mem hxN⟩ := eq_ggLAut_of_induces K θ hxN hxind
  have hψx : ggLAut K θ ⟨x, hxN⟩ = (u * f * u⁻¹)⁻¹ := by
    rw [hψ, ← map_inv]
    congr 1
    exact Subtype.ext (inv_inv x).symm
  have hB₁N : Bs ⊓ Subgroup.centralizer (X : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    fun b hb => hUK (hBsU hb.1)
  set E : Subgroup (MulAut R) := ((Bs ⊓ Subgroup.centralizer (X : Set G)).subgroupOf
    (Subgroup.normalizer (K : Set G))).map (ggLAut K θ) with hEdef
  have hmemE : ∀ e ∈ E, ∃ b ∈ Bs ⊓ Subgroup.centralizer (X : Set G),
      ∃ hb : b ∈ Subgroup.normalizer (K : Set G), ggLAut K θ ⟨b, hb⟩ = e := by
    rintro e ⟨g, hg, rfl⟩
    exact ⟨g, Subgroup.mem_subgroupOf.mp hg, g.2, rfl⟩
  have hEmem : ∀ b ∈ Bs ⊓ Subgroup.centralizer (X : Set G),
      ∀ hb : b ∈ Subgroup.normalizer (K : Set G), ggLAut K θ ⟨b, hb⟩ ∈ E :=
    fun b hb hbN => ⟨⟨b, hbN⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun e he => ?_⟩
    · obtain ⟨b₁, hb₁, hb₁N, hab⟩ := hmemE a a.2
      obtain ⟨b₂, hb₂, hb₂N, hbb⟩ := hmemE b b.2
      show (a : MulAut R) * b = b * a
      rw [← hab, ← hbb, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mul_comm_of_isElemAbelian hcfg.isElemAbelian hb₁.1 hb₂.1)
    · obtain ⟨b, hb, hbN, rfl⟩ := hmemE e he
      have h1 : (⟨b, hbN⟩ : Subgroup.normalizer (K : Set G)) ^ p = 1 :=
        Subtype.ext (by simpa using hcfg.isElemAbelian.2 b hb.1)
      rw [← map_pow, h1, map_one]
  have hEI : ∀ e ∈ E, e ∈ I := by
    intro e he
    obtain ⟨b, hb, hbN, rfl⟩ := hmemE e he
    exact ggLAut_mem_of_induces K θ hB₁N hB₁I hb
  have hEψ : ∀ e ∈ E, e * (u * f * u⁻¹) = u * f * u⁻¹ * e := by
    intro e he
    obtain ⟨b, hb, hbN, rfl⟩ := hmemE e he
    rw [hψ, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mul_comm_of_isElemAbelian hcfg.isElemAbelian hb.1
      (inv_mem hcfg.x_mem))
  have hH2 : ∀ r : R, MulAut.conj r ^ p = 1 →
      (∀ e ∈ E, MulAut.conj r * e = e * MulAut.conj r) →
      MulAut.conj r * (u * f * u⁻¹) = u * f * u⁻¹ * MulAut.conj r → MulAut.conj r ∈ E := by
    intro r hrp hrE hrψ
    obtain ⟨q, rfl⟩ := θ.surjective r
    induction q using QuotientGroup.induction_on with
    | H k =>
      have hρk := ggLAut_mk_self K θ k
      obtain ⟨j, -, hj⟩ := Nat.exists_mul_mod_eq_one_of_coprime hZ.symm hp.one_lt
      set N := Nat.card (Subgroup.center K) with hNdef
      set k₁ : G := (k : G) ^ (N * j) with hk₁
      have hk₁K : k₁ ∈ K := pow_mem k.2 _
      have hk₁N : k₁ ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hk₁K
      have hρk₁ : ggLAut K θ ⟨k₁, hk₁N⟩ = MulAut.conj (θ (k : K ⧸ Subgroup.center K)) := by
        have e : (⟨k₁, hk₁N⟩ : Subgroup.normalizer (K : Set G)) =
            ⟨k, Subgroup.le_normalizer k.2⟩ ^ (N * j) := Subtype.ext (by simp [hk₁])
        rw [e, map_pow, hρk, pow_eq_self_of_mod_eq_one hrp hj]
      have hkpN : ((k : G) ^ p) ^ N = 1 := by
        have hkpK : (k : G) ^ p ∈ K := pow_mem k.2 p
        have h1 : ggLAut K θ ⟨(k : G) ^ p, Subgroup.le_normalizer hkpK⟩ = 1 := by
          have e : (⟨(k : G) ^ p, Subgroup.le_normalizer hkpK⟩ :
              Subgroup.normalizer (K : Set G)) = ⟨k, Subgroup.le_normalizer k.2⟩ ^ p :=
            Subtype.ext (by simp)
          rw [e, map_pow, hρk, hrp]
        exact orderOf_dvd_iff_pow_eq_one.mp
          (orderOf_dvd_card_center hkpK (mem_centralizer_of_ggLAut_eq_one K θ hKp h1))
      have hk₁p : k₁ ^ p = 1 := by
        calc k₁ ^ p = (((k : G) ^ p) ^ N) ^ j := by
              rw [hk₁, ← pow_mul, ← pow_mul, ← pow_mul]
              congr 1
              ring
          _ = 1 := by rw [hkpN, one_pow]
      have hcomm : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (K : Set G)),
          ggLAut K θ ⟨g, hg⟩ * MulAut.conj (θ (k : K ⧸ Subgroup.center K)) =
            MulAut.conj (θ (k : K ⧸ Subgroup.center K)) * ggLAut K θ ⟨g, hg⟩ →
          g ∈ Subgroup.centralizer ({k₁} : Set G) := by
        intro g hg h
        rw [Subgroup.mem_centralizer_singleton_iff]
        refine commute_of_ggLAut_commute (θ := θ) hKp hZ hk₁K hk₁p hg ?_
        rw [hρk₁]
        exact h
      have hB₁k : Bs ⊓ Subgroup.centralizer (X : Set G) ≤ Subgroup.centralizer ({k₁} : Set G) :=
        fun b hb => hcomm b (hB₁N hb) (hrE _ (hEmem b hb (hB₁N hb))).symm
      have hxk : x ∈ Subgroup.centralizer ({k₁} : Set G) := by
        refine hcomm x hxN ?_
        rw [hψx]
        exact ((Commute.inv_right hrψ).eq).symm
      have hBsk : Bs ≤ Subgroup.centralizer ({k₁} : Set G) := by
        rw [hcfg.2.2.1.2]
        exact sup_le hB₁k (Subgroup.zpowers_le.mpr hxk)
      have hk₁C : k₁ ∈ Subgroup.centralizer (Bs : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact Subgroup.mem_centralizer_singleton_iff.mp (hBsk hb)
      have hk₁Bs : k₁ ∈ Bs := hcfg.bstar_max k₁ hk₁C hk₁p
      have hk₁U₁ : k₁ ∈ U₁ := (hiff k₁ (hBsU hk₁Bs) hk₁N).mpr (by rw [hρk₁]; exact hinn _)
      have hk₁B₁ := hcfg.inf_part_le hB₁U₁ hxU₁ ⟨hk₁Bs, hk₁U₁⟩
      rw [← hρk₁]
      exact hEmem k₁ hk₁B₁ hk₁N
  obtain ⟨n, hn⟩ := hTP hs hna f hf hord u hu E hEab hEI hEψ hH2
  have hρU₁ : ∀ (a : G) (ha : a ∈ U₁),
      ggLAut K θ ⟨a, hUK (hcfg.part_le ha)⟩ ∈ I ∧
        (∃ m : ℕ, ggLAut K θ ⟨a, hUK (hcfg.part_le ha)⟩ ^ p ^ m = 1) ∧
        ∀ e ∈ E, ggLAut K θ ⟨a, hUK (hcfg.part_le ha)⟩ * e =
          e * ggLAut K θ ⟨a, hUK (hcfg.part_le ha)⟩ := by
    intro a ha
    have haU := hcfg.part_le ha
    refine ⟨(hiff a haU (hUK haU)).mp ha, ?_, fun e he => ?_⟩
    · obtain ⟨m, hm⟩ := hcfg.isPGroup ⟨a, haU⟩
      refine ⟨m, ?_⟩
      have h1 : (⟨a, hUK haU⟩ : Subgroup.normalizer (K : Set G)) ^ p ^ m = 1 :=
        Subtype.ext (by simpa using congrArg Subtype.val hm)
      rw [← map_pow, h1, map_one]
    · obtain ⟨b, hb, hbN, rfl⟩ := hmemE e he
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext
        ((Subgroup.mem_centralizer_iff.mp (hcfg.le_centralizer haU) b hb).symm)
  refine ⟨fun a ha b hb => ?_, n, fun v hv => ?_⟩
  · obtain ⟨hsI, hsp, hsE⟩ := hρU₁ a ha
    obtain ⟨htI, htp, htE⟩ := hρU₁ b hb
    have hst := (hn _ hsI _ htI hsp htp hsE htE).1
    have haU := hcfg.part_le ha
    have hbU := hcfg.part_le hb
    have hmem : a * b * a⁻¹ * b⁻¹ ∈ U :=
      mul_mem (mul_mem (mul_mem haU hbU) (inv_mem haU)) (inv_mem hbU)
    refine ⟨hmem, mem_centralizer_of_ggLAut_eq_one K θ hKp (g := ⟨_, hUK hmem⟩) ?_⟩
    have e : (⟨a * b * a⁻¹ * b⁻¹, hUK hmem⟩ : Subgroup.normalizer (K : Set G)) =
        ⟨a, hUK haU⟩ * ⟨b, hUK hbU⟩ * (⟨a, hUK haU⟩ : Subgroup.normalizer (K : Set G))⁻¹ *
          (⟨b, hUK hbU⟩ : Subgroup.normalizer (K : Set G))⁻¹ := Subtype.ext rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hst]
    group
  · obtain ⟨hsI, hsp, hsE⟩ := hρU₁ v hv
    have h2 := (hn _ hsI _ hsI hsp hsp hsE hsE).2
    have hvU := hcfg.part_le hv
    have hmem : (v ^ n)⁻¹ * (x⁻¹ * v * x) ∈ U :=
      mul_mem (inv_mem (pow_mem hvU n)) (mul_mem (mul_mem (inv_mem hxU) hvU) hxU)
    refine ⟨hmem, mem_centralizer_of_ggLAut_eq_one K θ hKp (g := ⟨_, hUK hmem⟩) ?_⟩
    have e : (⟨(v ^ n)⁻¹ * (x⁻¹ * v * x), hUK hmem⟩ : Subgroup.normalizer (K : Set G)) =
        ((⟨v, hUK hvU⟩ : Subgroup.normalizer (K : Set G)) ^ n)⁻¹ *
          (⟨x⁻¹, inv_mem hxN⟩ * ⟨v, hUK hvU⟩ *
            (⟨x⁻¹, inv_mem hxN⟩ : Subgroup.normalizer (K : Set G))⁻¹) :=
      Subtype.ext (by simp)
    rw [e]
    simp only [map_mul, map_inv, map_pow]
    rw [← hψ, h2, inv_mul_cancel]

end Config

@[expose] def GGL45TorusCenterInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGL45Config p B Bs x L D J X B₂ d y K U U₁ → p ∣ Nat.card (Subgroup.center K) →
      (∀ a ∈ U₁, ∀ b ∈ U₁, a * b * a⁻¹ * b⁻¹ ∈ U ⊓ Subgroup.centralizer (K : Set G)) ∧
        ∃ e : ℕ, ∀ u ∈ U₁, (u ^ e)⁻¹ * (x⁻¹ * u * x) ∈ U ⊓ Subgroup.centralizer (K : Set G)

theorem ggL45TorusCenterInput_of_ab_pow (hab : GGL45TorusAbInput) (hpow : GGL45TorusPowInput) :
    GGL45TorusCenterInput :=
  fun G _ _ p B Bs x L D J X B₂ d y K U U₁ hcfg _ =>
    ⟨hab G p B Bs x L D J X B₂ d y K U U₁ hcfg, hpow G p B Bs x L D J X B₂ d y K U U₁ hcfg⟩

theorem ggL45TorusAbPow_of_raw (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hT : GGRawTorusPInput) (hc : GGL45TorusCenterInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) :
    (∀ a ∈ U₁, ∀ b ∈ U₁, a * b * a⁻¹ * b⁻¹ ∈ U ⊓ Subgroup.centralizer (K : Set G)) ∧
      ∃ e : ℕ, ∀ u ∈ U₁, (u ^ e)⁻¹ * (x⁻¹ * u * x) ∈ U ⊓ Subgroup.centralizer (K : Set G) := by
  by_cases hZ : Nat.Coprime p (Nat.card (Subgroup.center K))
  · exact hcfg.torusAbPow_of_coprime hraw hiso hT hZ
  · exact hc G p B Bs x L D J X B₂ d y K U U₁ hcfg
      (not_not.mp (mt (Nat.Prime.coprime_iff_not_dvd hcfg.prime).mpr hZ))

theorem ggL45TorusAbInput_of_raw (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hT : GGRawTorusPInput) (hc : GGL45TorusCenterInput) : GGL45TorusAbInput :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcfg => (ggL45TorusAbPow_of_raw hraw hiso hT hc hcfg).1

theorem ggL45TorusPowInput_of_raw (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hT : GGRawTorusPInput) (hc : GGL45TorusCenterInput) : GGL45TorusPowInput :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcfg => (ggL45TorusAbPow_of_raw hraw hiso hT hc hcfg).2

end CFSG.StandardType

end
