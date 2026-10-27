module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.AStar
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.QSylowW
public import CFSG.Mathlib.GroupTheory.InvolutionFrattini

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

private theorem mem_sup_iff_of_le_normalizer {G : Type*} [Group G] {H K : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (H : Set G)) {g : G} :
    g ∈ H ⊔ K ↔ ∃ x ∈ H, ∃ y ∈ K, g = x * y := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left H K hK, Set.mem_mul]
  exact ⟨fun ⟨x, hx, y, hy, hxy⟩ => ⟨x, hx, y, hy, hxy.symm⟩,
    fun ⟨x, hx, y, hy, hxy⟩ => ⟨x, hx, y, hy, hxy.symm⟩⟩

private theorem conj_mem_closure_of_cyclic {G : Type*} [Group G] {z : Fin 3 → G} {d : G}
    {σ : Fin 3 → Fin 3} (hσ : ∀ i, d * z i * d⁻¹ = z (σ i)) :
    ∀ x ∈ Subgroup.closure (Set.range z), d * x * d⁻¹ ∈ Subgroup.closure (Set.range z) := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      rw [hσ i]
      exact Subgroup.subset_closure ⟨σ i, rfl⟩
  | one => simp
  | mul y w _ _ ihy ihw =>
      rw [show d * (y * w) * d⁻¹ = (d * y * d⁻¹) * (d * w * d⁻¹) by group]
      exact mul_mem ihy ihw
  | inv y _ ihy =>
      rw [show d * y⁻¹ * d⁻¹ = (d * y * d⁻¹)⁻¹ by group]
      exact inv_mem ihy

private theorem card_sup_of_le_normalizer {G : Type*} [Group G] {H K : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (H : Set G)) (hi : H ⊓ K = ⊥) :
    Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  let f : ↥H × ↥K → ↥(H ⊔ K) := fun p =>
    ⟨(p.1 : G) * p.2, mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨x, y⟩ ⟨x', y'⟩ hxy
      have h1 : ((x : G) * y) = x' * y' := congrArg Subtype.val hxy
      have h2 : (x' : G)⁻¹ * x = y' * (y : G)⁻¹ := by
        calc (x' : G)⁻¹ * x = (x' : G)⁻¹ * (x * y) * (y : G)⁻¹ := by group
          _ = (x' : G)⁻¹ * (x' * y') * (y : G)⁻¹ := by rw [h1]
          _ = y' * (y : G)⁻¹ := by group
      have hmem : (x' : G)⁻¹ * x ∈ H ⊓ K :=
        Subgroup.mem_inf.2 ⟨mul_mem (inv_mem x'.2) x.2,
          h2 ▸ mul_mem y'.2 (inv_mem y.2)⟩
      rw [hi, Subgroup.mem_bot] at hmem
      have hx : (x : G) = x' := by
        rw [← mul_inv_cancel_left (x' : G) x, hmem, mul_one]
      have hy : (y : G) = y' := by
        rw [hx] at h1
        exact mul_left_cancel h1
      simp only [Prod.mk.injEq]
      exact ⟨Subtype.ext hx, Subtype.ext hy⟩
    · rintro ⟨g, hg⟩
      obtain ⟨x, hx, y, hy, rfl⟩ := (mem_sup_iff_of_le_normalizer hK).1 hg
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
  rw [← Nat.card_prod, Nat.card_congr (Equiv.ofBijective f hf)]

theorem maximal_in_normalizer {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {B₂ A : Subgroup G} {τ c : G}
    (hB₂ : B2Package b z B₂) (hA : AStar b z B₂ A) (hτc : TauC z τ c) :
    ∀ R : Subgroup G, R ≤ Subgroup.normalizer (B₂ : Set G) → IsPGroup 3 R →
      A ⊔ (Subgroup.zpowers b ⊔ Subgroup.zpowers c) ≤ R →
        R = A ⊔ (Subgroup.zpowers b ⊔ Subgroup.zpowers c) := by
  intro R hRN hR hP₀R
  let C₂ : Subgroup G := Subgroup.centralizer (B₂ : Set G)
  let N₂ : Subgroup G := Subgroup.normalizer (B₂ : Set G)
  let W : Subgroup G := Subgroup.centralizer ({τ} : Set G) ⊓ N₂
  let Q : Subgroup G := Subgroup.zpowers b ⊔ Subgroup.zpowers c
  let P₀ : Subgroup G := A ⊔ Q
  change R = P₀
  have hC₂N : C₂ ≤ N₂ := Subgroup.centralizer_le_normalizer (B₂ : Set G)
  have hc_nor_bOne : c ∈ Subgroup.normalizer ((bOne z : Subgroup G) : Set G) := by
    have hσ : ∀ i : Fin 3, c * GGFF.zs z i * c⁻¹ = GGFF.zs z (![1, 2, 0] i) := by
      intro i
      fin_cases i <;> simp [hτc.cyc₀, hτc.cyc₁, hτc.cyc₂]
    have hσ' : ∀ i : Fin 3, c⁻¹ * GGFF.zs z i * (c⁻¹)⁻¹ = GGFF.zs z (![2, 0, 1] i) := by
      have hc₀ : c⁻¹ * GGFF.zs z 0 * c = GGFF.zs z 2 := by rw [← hτc.cyc₂]; group
      have hc₁ : c⁻¹ * GGFF.zs z 1 * c = GGFF.zs z 0 := by rw [← hτc.cyc₀]; group
      have hc₂ : c⁻¹ * GGFF.zs z 2 * c = GGFF.zs z 1 := by rw [← hτc.cyc₁]; group
      intro i
      rw [inv_inv]
      fin_cases i <;> simp [hc₀, hc₁, hc₂]
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact conj_mem_closure_of_cyclic hσ x
    · intro hx
      have h := conj_mem_closure_of_cyclic (d := c⁻¹) hσ' (c * x * c⁻¹) hx
      rw [show c⁻¹ * (c * x * c⁻¹) * (c⁻¹)⁻¹ = x by group] at h
      exact h
  have hbN : b ∈ N₂ :=
    Subgroup.mem_normalizer_fintype (fun x hx => hB₂.b_nor x hx)
  have hcN : c ∈ N₂ :=
    Subgroup.mem_normalizer_fintype (fun x hx =>
      hB₂.D_nor c (Subgroup.mem_inf.mpr ⟨hτc.c_mem, hc_nor_bOne⟩) x hx)
  have hτN : τ ∈ N₂ :=
    Subgroup.mem_normalizer_fintype (fun x hx => by
      rw [hB₂.tau_inv τ hτc.tau_mem hτc.inv x hx]
      exact B₂.inv_mem hx)
  have hbC : b ∈ Subgroup.centralizer ({τ} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact (Subgroup.mem_centralizer_iff.mp (h.hypA.le hτc.tau_mem) b rfl).symm
  have hcC : c ∈ Subgroup.centralizer ({τ} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hτc.comm.symm
  have hQW : Q ≤ W := by
    dsimp only [Q]
    exact sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hbC, hbN⟩))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hcC, hcN⟩))
  have hb3 : IsPGroup 3 (Subgroup.zpowers b : Subgroup G) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.hypA.ord]; norm_num)
  have hc3 : IsPGroup 3 (Subgroup.zpowers c : Subgroup G) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hτc.c_cube)
  have hnorm_bc : Subgroup.zpowers c ≤ Subgroup.normalizer (Subgroup.zpowers b : Subgroup G) := by
    refine (Subgroup.zpowers_le.mpr (h.hypA.le hτc.c_mem)).trans ?_
    rw [Subgroup.zpowers_eq_closure b]
    exact (Subgroup.centralizer_le_normalizer ({b} : Set G)).trans
      (Subgroup.normalizer_le_normalizer_closure ({b} : Set G))
  have hQisP : IsPGroup 3 Q := by
    dsimp only [Q]
    exact hb3.to_sup_of_normal_left' hc3 hnorm_bc
  have hcD : c ∈ dGrp b z :=
    Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hτc.c_mem, hc_nor_bOne⟩)
  have hQd : Q ≤ dGrp b z := by
    dsimp only [Q]
    exact sup_le le_sup_left (Subgroup.zpowers_le.mpr hcD)
  have hQnormA : Q ≤ Subgroup.normalizer (A : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hA.nor q (hQd hq) x hx
    · intro hx
      have hq' : q⁻¹ ∈ Q := Q.inv_mem hq
      have hmem := hA.nor q⁻¹ (hQd hq') (q * x * q⁻¹) hx
      have heq : q⁻¹ * (q * x * q⁻¹) * (q⁻¹)⁻¹ = x := by group
      rwa [heq] at hmem
  have hAQ : A ⊓ Q = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro q hq
    by_contra hq1
    have hqQ : q ∈ Q := hq.2
    have hqA : q ∈ A := hq.1
    have hqC : q ∈ C₂ := hA.le_cen hqA
    have hB2le : B₂ ≤ Subgroup.centralizer ({q} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (Subgroup.mem_centralizer_iff.mp hqC x hx).symm
    have hcard : Nat.card ↥(B₂ ⊓ Subgroup.centralizer ({q} : Set G)) = 3 ^ 6 := by
      rw [inf_eq_left.mpr hB2le, hB₂.card]
    have hle := card_centralizer_le h hB₂ hτc hqQ hq1
    rw [hcard] at hle
    norm_num at hle
  have hAN : A ≤ N₂ := hA.le_cen.trans hC₂N
  have hQN : Q ≤ N₂ := hQW.trans inf_le_right
  have hP₀N : P₀ ≤ N₂ := by
    dsimp only [P₀]
    exact sup_le hAN hQN
  have hfrattini : ∀ g ∈ N₂, ∃ w ∈ W, ∃ y ∈ C₂, g = w * y := by
    intro g hg
    have hgx : ∀ x ∈ B₂, g * x * g⁻¹ ∈ B₂ := fun x hx =>
      (Subgroup.mem_normalizer_iff.mp hg x).mp hx
    have huC : g⁻¹ * τ * g * τ⁻¹ ∈ C₂ := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hAinv : (g⁻¹ * τ * g) * x * (g⁻¹ * τ * g)⁻¹ = x⁻¹ := by
        have hτ := hB₂.tau_inv τ hτc.tau_mem hτc.inv (g * x * g⁻¹) (hgx x hx)
        calc (g⁻¹ * τ * g) * x * (g⁻¹ * τ * g)⁻¹
            = g⁻¹ * (τ * (g * x * g⁻¹) * τ⁻¹) * g := by group
          _ = g⁻¹ * (g * x * g⁻¹)⁻¹ * g := by rw [hτ]
          _ = x⁻¹ := by group
      have hτinv : τ * x * τ⁻¹ = x⁻¹ := hB₂.tau_inv τ hτc.tau_mem hτc.inv x hx
      have hτinv' : τ⁻¹ * x * τ = x⁻¹ := by
        have hτ : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hτc.tau_sq)
        simpa [hτ] using hτinv
      have hux : (g⁻¹ * τ * g * τ⁻¹) * x * (g⁻¹ * τ * g * τ⁻¹)⁻¹ = x := by
        have hAinv' : (g⁻¹ * τ * g) * x⁻¹ * (g⁻¹ * τ * g)⁻¹ = x := by
          rw [show (g⁻¹ * τ * g) * x⁻¹ * (g⁻¹ * τ * g)⁻¹ =
                ((g⁻¹ * τ * g) * x * (g⁻¹ * τ * g)⁻¹)⁻¹ by group, hAinv]
          group
        calc (g⁻¹ * τ * g * τ⁻¹) * x * (g⁻¹ * τ * g * τ⁻¹)⁻¹
            = (g⁻¹ * τ * g) * (τ⁻¹ * x * τ) * (g⁻¹ * τ * g)⁻¹ := by group
          _ = (g⁻¹ * τ * g) * x⁻¹ * (g⁻¹ * τ * g)⁻¹ := by rw [hτinv']
          _ = x := hAinv'
      have hxu : g⁻¹ * τ * g * τ⁻¹ * x = x * (g⁻¹ * τ * g * τ⁻¹) := by
        calc g⁻¹ * τ * g * τ⁻¹ * x
            = g⁻¹ * τ * g * τ⁻¹ * x * (g⁻¹ * τ * g * τ⁻¹)⁻¹ * (g⁻¹ * τ * g * τ⁻¹) := by
              group
          _ = x * (g⁻¹ * τ * g * τ⁻¹) := by rw [hux]
      exact hxu.symm
    obtain ⟨y, hyC, w, hwcen, hgw⟩ :=
      CFSG.InvolutionFrattini.exists_mul_centralizer_of_conj_mem_coset C₂
        (odd_cen_b2 h hB₂) hτc.tau_sq huC
    have hwN : w ∈ N₂ := by
      have hw : w = g * y⁻¹ := by rw [hgw]; group
      rw [hw]
      exact N₂.mul_mem hg (N₂.inv_mem (hC₂N hyC))
    exact ⟨w, Subgroup.mem_inf.mpr ⟨hwcen, hwN⟩, y, hyC, hgw⟩
  let C₂N : Subgroup ↥N₂ := C₂.subgroupOf N₂
  have hWN : W ≤ N₂ := inf_le_right
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' C₂N).comp (Subgroup.inclusion hWN) : ↥W →* ↥N₂ ⧸ C₂N) := by
    intro x
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective C₂N x
    obtain ⟨w, hwW, y, hyC, hgw⟩ := hfrattini (g : G) g.2
    refine ⟨⟨w, hwW⟩, ?_⟩
    rw [← hg]
    simp only [MonoidHom.comp_apply]
    rw [QuotientGroup.mk'_eq_mk']
    refine ⟨⟨y, hC₂N hyC⟩, Subgroup.mem_subgroupOf.mpr hyC, ?_⟩
    apply Subtype.ext
    show w * y = (g : G)
    exact hgw.symm
  have hquot_dvd_W : Nat.card (↥N₂ ⧸ C₂N) ∣ Nat.card W :=
    Subgroup.card_dvd_of_surjective hsurj
  have hAR : A ≤ R := le_sup_left.trans hP₀R
  have hRcen : R ⊓ C₂ = A :=
    hA.max (R ⊓ C₂) inf_le_right hR.to_inf_left (le_inf hAR hA.le_cen)
  let φ : ↥R →* ↥N₂ ⧸ C₂N := (QuotientGroup.mk' C₂N).comp (Subgroup.inclusion hRN)
  have hker : φ.ker = A.subgroupOf R := by
    ext x
    constructor
    · intro hx
      have hx1 : φ x = 1 := MonoidHom.mem_ker.mp hx
      have hx2 : QuotientGroup.mk' C₂N (Subgroup.inclusion hRN x) = 1 := by
        simpa only [φ, MonoidHom.comp_apply] using hx1
      have h1 : (Subgroup.inclusion hRN x : ↥N₂) ∈ C₂N :=
        (QuotientGroup.eq_one_iff (N := C₂N) (Subgroup.inclusion hRN x)).mp hx2
      have h2 : (x : G) ∈ C₂ := by
        have := Subgroup.mem_subgroupOf.mp h1
        simpa using this
      have h3 : (x : G) ∈ R ⊓ C₂ := ⟨x.2, h2⟩
      rwa [hRcen] at h3
    · intro hx
      have hxA : (x : G) ∈ A := Subgroup.mem_subgroupOf.mp hx
      have hxC : (x : G) ∈ C₂ := hA.le_cen hxA
      have h1 : (Subgroup.inclusion hRN x : ↥N₂) ∈ C₂N := Subgroup.mem_subgroupOf.mpr hxC
      have hx2 : QuotientGroup.mk' C₂N (Subgroup.inclusion hRN x) = 1 :=
        (QuotientGroup.eq_one_iff (N := C₂N) (Subgroup.inclusion hRN x)).mpr h1
      exact MonoidHom.mem_ker.mpr (by simpa only [φ, MonoidHom.comp_apply] using hx2)
  have hcard_ker : Nat.card φ.ker = Nat.card A := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAR).toEquiv
  have hcardR : Nat.card R = Nat.card A * Nat.card φ.range := by
    rw [← Subgroup.card_ker_mul_card_range φ, hcard_ker]
  have h_range_isP : IsPGroup 3 φ.range :=
    hR.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 3) (G := φ.range)).mp h_range_isP
  have h_range_dvd_W : Nat.card φ.range ∣ Nat.card W :=
    (Subgroup.card_subgroup_dvd_card φ.range).trans hquot_dvd_W
  have h3j_dvd_W : 3 ^ j ∣ Nat.card W := by
    rw [← hj]
    exact h_range_dvd_W
  have hj_le : j ≤ (Nat.card W).factorization 3 :=
    (Nat.prime_three.pow_dvd_iff_le_factorization (Nat.card_pos (α := W)).ne').mp h3j_dvd_W
  have hQsub_isP : IsPGroup 3 (Q.subgroupOf W) :=
    hQisP.of_equiv (Subgroup.subgroupOfEquivOfLe hQW).symm
  obtain ⟨S, hQS⟩ := IsPGroup.exists_le_sylow hQsub_isP
  have hSmap_le_W : (S : Subgroup ↥W).map W.subtype ≤ W := Subgroup.map_subtype_le _
  have hSmap_isP : IsPGroup 3 ((S : Subgroup ↥W).map W.subtype) := S.isPGroup'.map W.subtype
  have hQ_le_Smap : Q ≤ (S : Subgroup ↥W).map W.subtype := by
    intro q hq
    have hqW : q ∈ W := hQW hq
    exact Subgroup.mem_map.mpr ⟨⟨q, hqW⟩, hQS hq, rfl⟩
  have hSeq : (S : Subgroup ↥W).map W.subtype = Q :=
    maximal_in_cen_tau h hB₂ hτc _ hSmap_le_W hSmap_isP hQ_le_Smap
  have hQcard : Nat.card Q = 3 ^ (Nat.card W).factorization 3 := by
    rw [← hSeq]
    rw [Subgroup.card_map_of_injective W.subtype_injective]
    exact Sylow.card_eq_multiplicity S
  have h_range_le_Q : Nat.card φ.range ≤ Nat.card Q := by
    rw [hj, hQcard]
    exact Nat.pow_le_pow_right (by norm_num : 0 < 3) hj_le
  have hPcard : Nat.card P₀ = Nat.card A * Nat.card Q := by
    dsimp only [P₀]
    exact card_sup_of_le_normalizer hQnormA hAQ
  have hRcard_le : Nat.card R ≤ Nat.card P₀ := by
    rw [hcardR, hPcard]
    exact Nat.mul_le_mul_left _ h_range_le_Q
  exact (Subgroup.eq_of_le_of_card_ge hP₀R hRcard_le).symm

end CFSG.StandardType.FF81.PropOne

end
