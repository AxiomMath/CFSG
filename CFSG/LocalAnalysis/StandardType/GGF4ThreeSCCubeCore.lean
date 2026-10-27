module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGOneFiveRank
import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBTypeALabel
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem exists_transvection_of_SC_cube {p : ℕ} (hp : p.Prime)
    {E T : Subgroup G} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3)
    (hT : IsElemAbelian p T) (hTlarge : p ^ 4 ≤ Nat.card T)
    (hN : E ≤ Subgroup.normalizer (T : Set G))
    (hSC : ∀ g ∈ Subgroup.centralizer (E : Set G), g ^ p = 1 → g ∈ E) :
    ∃ φ ∈ ggInduced ⊤ E, GGIsTransvection p φ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hHp : IsPGroup p (T ⊔ E : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hT.isPGroup hE.isPGroup hN
  have hTE : ¬ T ≤ E := by
    intro hle
    have h1 : Nat.card T ≤ Nat.card E := Subgroup.card_le_of_le hle
    rw [hcard] at h1
    have h2 : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  have hElt : E < T ⊔ E := by
    refine lt_of_le_of_ne le_sup_right ?_
    intro heq
    exact hTE (le_sup_left.trans heq.ge)
  obtain ⟨n, hnH, hnN, hnE⟩ := exists_mem_normalizer_not_mem hHp hElt
  have hHE := Subgroup.coe_mul_of_right_le_normalizer_left T E hN
  have hnH' : n ∈ (↑(T ⊔ E) : Set G) := hnH
  rw [hHE] at hnH'
  obtain ⟨t, htT, e, heE, hte⟩ := Set.mem_mul.mp hnH'
  have heN : e ∈ Subgroup.normalizer (E : Set G) := Subgroup.le_normalizer heE
  have htN : t ∈ Subgroup.normalizer (E : Set G) := by
    have h1 : t * e ∈ Subgroup.normalizer (E : Set G) := hte ▸ hnN
    have h2 : (t * e) * e⁻¹ ∈ Subgroup.normalizer (E : Set G) :=
      Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ heN)
    simpa [mul_assoc] using h2
  have htE : t ∉ E := by
    intro htE'
    exact hnE (hte ▸ E.mul_mem htE' heE)
  have htk : t ^ p = 1 := hT.2 t htT
  have htC : t ∉ Subgroup.centralizer (E : Set G) := by
    intro htC'
    exact htE (hSC t htC' htk)
  let δ : ↥E →* ↥E :=
    { toFun := fun x => x⁻¹ * ggConjAut E htN x
      map_one' := by simp
      map_mul' := fun a b => by
        have hcomm : ∀ a b : ↥E, a * b = b * a := fun a b => hE.1.is_comm.comm a b
        simp only [map_mul, mul_inv_rev]
        calc b⁻¹ * a⁻¹ * (ggConjAut E htN a * ggConjAut E htN b)
            = b⁻¹ * (a⁻¹ * ggConjAut E htN a) * ggConjAut E htN b := by group
          _ = (a⁻¹ * ggConjAut E htN a) * b⁻¹ * ggConjAut E htN b := by rw [hcomm b⁻¹]
          _ = a⁻¹ * ggConjAut E htN a * (b⁻¹ * ggConjAut E htN b) := by group }
  have hδ : ∀ x : ↥E, δ x = x⁻¹ * ggConjAut E htN x := fun _ => rfl
  have hδT : ∀ x : ↥E, ((δ x : ↥E) : G) ∈ T := by
    intro x
    have hxt : (x : G)⁻¹ * t * (x : G) ∈ T := by
      have h := (Subgroup.mem_normalizer_iff.mp (hN (E.inv_mem x.2)) t).mp htT
      simpa using h
    have hx : ((δ x : ↥E) : G) = (x : G)⁻¹ * t * (x : G) * t⁻¹ := by
      rw [hδ]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, ggConjAut_apply]
      group
    rw [hx]
    exact T.mul_mem hxt (T.inv_mem htT)
  have hfix : ∀ b : ↥E, δ b = 1 ↔ ggConjAut E htN b = b := fun b => by
    rw [hδ b, inv_mul_eq_one, eq_comm]
  have hδ2 : δ.range ≤ δ.ker := by
    rintro y ⟨x, rfl⟩
    rw [MonoidHom.mem_ker, hfix]
    apply Subtype.ext
    rw [ggConjAut_apply]
    have hxT : ((δ x : ↥E) : G) ∈ T := hδT x
    have hcomm := hT.1.is_comm.comm ⟨t, htT⟩ ⟨(δ x : ↥E), hxT⟩
    have h1 : t * ((δ x : ↥E) : G) = ((δ x : ↥E) : G) * t := congrArg Subtype.val hcomm
    rw [h1]
    group
  have hrange_ne_bot : δ.range ≠ ⊥ := by
    intro hbot
    apply htC
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxrange : δ ⟨x, hx⟩ ∈ δ.range := ⟨⟨x, hx⟩, rfl⟩
    rw [hbot] at hxrange
    have hx1 : δ ⟨x, hx⟩ = 1 := by simpa using hxrange
    rw [hfix] at hx1
    have h1 : t * (x : G) * t⁻¹ = (x : G) := by
      have := congrArg (fun z : ↥E => (z : G)) hx1
      simpa [ggConjAut_apply] using this
    show (x : G) * t = t * (x : G)
    calc (x : G) * t = (t * (x : G) * t⁻¹) * t := by rw [h1]
      _ = t * (x : G) := by group
  have hcardmul : Nat.card δ.ker * Nat.card δ.range = Nat.card ↥E :=
    Subgroup.card_ker_mul_card_range δ
  have hle : Nat.card δ.range ≤ Nat.card δ.ker := Subgroup.card_le_of_le hδ2
  have hsq : Nat.card δ.range ^ 2 ≤ p ^ 3 := by
    calc Nat.card δ.range ^ 2 = Nat.card δ.range * Nat.card δ.range := by rw [pow_two]
      _ ≤ Nat.card δ.range * Nat.card δ.ker := Nat.mul_le_mul_left _ hle
      _ = Nat.card δ.ker * Nat.card δ.range := Nat.mul_comm _ _
      _ = Nat.card ↥E := hcardmul
      _ = p ^ 3 := hcard
  have hrange_dvd_E : Nat.card δ.range ∣ Nat.card ↥E := Subgroup.card_subgroup_dvd_card δ.range
  have hrange_dvd_p : Nat.card δ.range ∣ p ^ 3 := by
    rw [← hcard]
    exact hrange_dvd_E
  obtain ⟨m, hm3, hm⟩ := (Nat.dvd_prime_pow hp).mp hrange_dvd_p
  have hm_le : m ≤ 1 := by
    have h2 : p ^ (2 * m) ≤ p ^ 3 := by
      have h := hsq
      rw [hm, ← pow_mul, mul_comm m 2] at h
      exact h
    have h3 : 2 * m ≤ 3 := (Nat.pow_le_pow_iff_right hp.one_lt).mp h2
    omega
  have hrange_dvd : Nat.card δ.range ∣ p := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · rw [hm, hm0, pow_zero]
      exact one_dvd p
    · have hm1 : m = 1 := by omega
      rw [hm, hm1, pow_one]
  have hrange_eq : Nat.card δ.range = p := by
    rcases (Nat.dvd_prime hp).mp hrange_dvd with h1 | h1
    · exact absurd h1 (fun h => hrange_ne_bot (Subgroup.card_eq_one.mp h))
    · exact h1
  have hfixcard : Nat.card {b : ↥E // ggConjAut E htN b = b} = Nat.card δ.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight fun b => (hfix b).symm.trans MonoidHom.mem_ker.symm)
  refine ⟨ggConjAut E htN, ggConjAut_mem_ggInduced (Subgroup.mem_top t) htN, ?_, ?_⟩
  · rw [hfixcard, ← hcardmul, hrange_eq]
  · intro b
    rw [← hδ b]
    apply Subtype.ext
    rw [ggConjAut_apply]
    have hbT : ((δ b : ↥E) : G) ∈ T := hδT b
    have hcomm := hT.1.is_comm.comm ⟨t, htT⟩ ⟨(δ b : ↥E), hbT⟩
    have h1 : t * ((δ b : ↥E) : G) = ((δ b : ↥E) : G) * t := congrArg Subtype.val hcomm
    rw [h1]
    group

theorem exists_transvection_of_SC_cube_sylow {p : ℕ} (hp : p.Prime)
    {P : Sylow p G} {T : Subgroup G} (hT : IsElemAbelian p T)
    (hTlarge : p ^ 4 ≤ Nat.card T)
    (hPT : (P : Subgroup G) ≤ Subgroup.normalizer (T : Set G))
    {E : Subgroup G} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3)
    (hSC : ∀ g ∈ Subgroup.centralizer (E : Set G), g ^ p = 1 → g ∈ E) :
    ∃ φ ∈ ggInduced ⊤ E, GGIsTransvection p φ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hEQ⟩ := hE.isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  have hconj : ∀ q ∈ E, g * q * g⁻¹ ∈ (P : Subgroup G) := by
    intro q hq
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hEQ hq
  let σ : G ≃* G := MulAut.conj g
  let E' : Subgroup G := E.map (σ : G →* G)
  have hE'P : E' ≤ (P : Subgroup G) := by
    rintro _ ⟨q, hq, rfl⟩
    simpa [σ, MulAut.conj_apply] using hconj q hq
  have hE'el : IsElemAbelian p E' := hE.map σ.toMonoidHom
  have hE'card : Nat.card E' = p ^ 3 := by
    rw [Subgroup.card_map_of_injective σ.injective, hcard]
  have hSC' : ∀ k ∈ Subgroup.centralizer (E' : Set G), k ^ p = 1 → k ∈ E' := by
    intro k hk hkp
    have h0C : g⁻¹ * k * g ∈ Subgroup.centralizer (E : Set G) := by
      rw [Subgroup.mem_centralizer_iff] at hk ⊢
      intro x hx
      have hx' : g * x * g⁻¹ ∈ E' := ⟨x, hx, rfl⟩
      have hcomm := hk (g * x * g⁻¹) hx'
      calc x * (g⁻¹ * k * g) = g⁻¹ * ((g * x * g⁻¹) * k) * g := by group
        _ = g⁻¹ * (k * (g * x * g⁻¹)) * g := by rw [hcomm]
        _ = (g⁻¹ * k * g) * x := by group
    have h0p : (g⁻¹ * k * g) ^ p = 1 := by
      have hc : g⁻¹ * k * g = g⁻¹ * k * (g⁻¹)⁻¹ := by group
      rw [hc, conj_pow, hkp, mul_one, mul_inv_cancel]
    exact ⟨g⁻¹ * k * g, hSC _ h0C h0p, by
      change σ (g⁻¹ * k * g) = k
      simp only [σ, MulAut.conj_apply]
      group⟩
  obtain ⟨ψ', hψ'mem, hψ'trans⟩ :=
    exists_transvection_of_SC_cube hp hE'el hE'card hT hTlarge (hE'P.trans hPT) hSC'
  obtain ⟨h, -, hhN', hhφ⟩ := hψ'mem
  set h' : G := g⁻¹ * h * g with hh'def
  have hh'N : h' ∈ Subgroup.normalizer (E : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hx' : σ x ∈ E' := ⟨x, hx, rfl⟩
      have h2 : h * σ x * h⁻¹ ∈ E' := (Subgroup.mem_normalizer_iff.mp hhN' (σ x)).mp hx'
      obtain ⟨y, hy, hyeq⟩ := h2
      have hy' : σ y = h * σ x * h⁻¹ := hyeq
      have hxy : h' * x * h'⁻¹ = y := by
        rw [hh'def]
        have key : (g⁻¹ * h * g) * x * (g⁻¹ * h * g)⁻¹ = g⁻¹ * (h * σ x * h⁻¹) * g := by
          simp only [σ, MulAut.conj_apply]
          group
        rw [key, ← hy']
        simp only [σ, MulAut.conj_apply]
        group
      rwa [hxy]
    · intro hx
      have hx'' : h * σ x * h⁻¹ ∈ E' := by
        refine ⟨h' * x * h'⁻¹, hx, ?_⟩
        rw [hh'def]
        change σ (g⁻¹ * h * g * x * (g⁻¹ * h * g)⁻¹) = h * σ x * h⁻¹
        simp only [σ, MulAut.conj_apply]
        group
      have hx''' : σ x ∈ E' := (Subgroup.mem_normalizer_iff.mp hhN' (σ x)).mpr hx''
      obtain ⟨y, hy, hyeq⟩ := hx'''
      have hyx : y = x := σ.injective (by simpa [σ] using hyeq)
      rwa [← hyx]
  refine ⟨ggConjAut E hh'N, ggConjAut_mem_ggInduced (Subgroup.mem_top h') hh'N, ?_⟩
  have hf : ∀ e : ↥E', ggConjAut E hh'N ((σ.subgroupMap E).symm e) =
      (σ.subgroupMap E).symm (ψ' e) := by
    intro e
    apply (σ.subgroupMap E).injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [MulEquiv.coe_subgroupMap_apply, hhφ e]
    have h2 : σ (((σ.subgroupMap E).symm e : ↥E) : G) = (e : G) := by
      have h1 : ((σ.subgroupMap E) ((σ.subgroupMap E).symm e) : ↥E') = e :=
        MulEquiv.apply_symm_apply _ _
      have := congrArg (fun z : ↥E' => (z : G)) h1
      rwa [MulEquiv.coe_subgroupMap_apply] at this
    have h4 : σ h' = h := by
      rw [hh'def]
      simp only [σ, MulAut.conj_apply]
      group
    rw [ggConjAut_apply]
    simp only [map_mul, map_inv]
    rw [h2, h4]
  exact GGIsTransvection.of_mulEquiv (σ.subgroupMap E).symm hf hψ'trans

end CFSG.StandardType
