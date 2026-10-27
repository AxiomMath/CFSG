module

public import CFSG.Quasithin.Recognition.F112WChief
public import CFSG.GroupTheory.WielandtProductBasic

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type*} [Group G] [Finite G]

private theorem eq_top_of_isPGroup_quotient {H : Type*} [Group H] [Finite H] {S K : Subgroup H}
    [K.Normal] (hSK : S ≤ K) (hodd : ¬ 2 ∣ S.index) (hK : IsPGroup 2 (H ⧸ K)) : K = ⊤ := by
  have hdvd : K.index ∣ S.index := Subgroup.index_dvd_of_le hSK
  have hoddK : ¬ 2 ∣ K.index := fun h => hodd (h.trans hdvd)
  obtain ⟨n, hn⟩ := hK.exists_card_dvd_pow
  have hKpow : K.index ∣ 2 ^ n := by rwa [Subgroup.index_eq_card]
  have hoddK' : Odd K.index :=
    Nat.coprime_two_left.mp ((Nat.prime_two.coprime_iff_not_dvd).mpr hoddK)
  have hcop2 : Nat.Coprime K.index 2 := Nat.coprime_comm.mp (Nat.coprime_two_left.mpr hoddK')
  have hcop : Nat.Coprime K.index (2 ^ n) := hcop2.pow_right n
  have hK1 : K.index = 1 := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hKpow
  exact Subgroup.index_eq_one.mp hK1

theorem commutator_le_of_isCentralStep_of_isSylow
    {H S U N K : Subgroup G} {x : G}
    (hS : IsSylowTwoOf S H) (hUH : U ≤ H) (hU : IsElemAbelian 2 U)
    (hN : IsNormalIn H U N) (hK : IsNormalIn H U K) (hNK : N ≤ K) (hKU : K ≤ U)
    (hcent : IsCentralStep H N K)
    (hxK : ∀ h ∈ H, h * x * h⁻¹ * x⁻¹ ∈ K)
    (hxS : ∀ s ∈ S, s * x * s⁻¹ * x⁻¹ ∈ N) :
    ∀ h ∈ H, h * x * h⁻¹ * x⁻¹ ∈ N := by
  classical
  have hKN : K ≤ Subgroup.normalizer (N : Set G) :=
    (hKU.trans hUH).trans (D14.le_normalizer_of_isNormalIn (H := H) (U := U) hN)
  letI : (N.subgroupOf K).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hKN
  have hxK' : ∀ h : H, (h : G) * x * (h : G)⁻¹ * x⁻¹ ∈ K := fun h => hxK h h.2
  let δ : H →* K ⧸ N.subgroupOf K :=
    MonoidHom.mk' (fun h : H => QuotientGroup.mk ⟨(h : G) * x * (h : G)⁻¹ * x⁻¹, hxK' h⟩) (by
      intro g h
      apply QuotientGroup.eq.mpr
      rw [Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
      set a : G := ((g : G) * (h : G)) * x * ((g : G) * (h : G))⁻¹ * x⁻¹ with ha_def
      set b : G := (h : G) * x * (h : G)⁻¹ * x⁻¹ with hb_def
      set c : G := (g : G) * x * (g : G)⁻¹ * x⁻¹ with hc_def
      have hbK : b ∈ K := hxK' h
      have hcK : c ∈ K := hxK' g
      have haK : a ∈ K := by
        simpa [ha_def, Subgroup.coe_mul] using hxK' (g * h)
      have h1 : g * b * (g : G)⁻¹ * b⁻¹ ∈ N := hcent g g.2 b hbK
      have h2 : b * c * b⁻¹ * c⁻¹ ∈ N := hcent b (hUH (hKU hbK)) c hcK
      have h3 : a * (c * b)⁻¹ ∈ N := by
        have e : a * (c * b)⁻¹ = (g * b * (g : G)⁻¹ * b⁻¹) * (b * c * b⁻¹ * c⁻¹) := by
          rw [ha_def, hb_def, hc_def]; group
        rw [e]
        exact N.mul_mem h1 h2
      have h4 : (c * b) * a⁻¹ ∈ N := by simpa using N.inv_mem h3
      have h5 : (a⁻¹ : G) * ((c * b) * a⁻¹) * a ∈ N := by
        simpa using
          (Subgroup.mem_normalizer_iff.mp (hKN (K.inv_mem haK)) ((c * b) * a⁻¹)).mp h4
      have e2 : (a⁻¹ : G) * (c * b) = a⁻¹ * ((c * b) * a⁻¹) * a := by group
      have hfinal : (a⁻¹ : G) * (c * b) ∈ N := by rw [e2]; exact h5
      simpa [ha_def] using hfinal)
  have hSker : S.subgroupOf H ≤ δ.ker := by
    intro s hs
    rw [MonoidHom.mem_ker]
    change QuotientGroup.mk (⟨(s : G) * x * (s : G)⁻¹ * x⁻¹, hxK' s⟩ : ↥K) = 1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hxS (s : G) (Subgroup.mem_subgroupOf.mp hs)
  have hK2 : IsPGroup 2 ↥K := fun k => ⟨1, by
    apply Subtype.ext
    have := hU.2 k.1 (hKU k.2)
    simpa using this⟩
  have hQ2 : IsPGroup 2 (K ⧸ N.subgroupOf K) := hK2.to_quotient _
  have hP : IsPGroup 2 (H ⧸ δ.ker) :=
    IsPGroup.of_injective hQ2 (QuotientGroup.kerLift δ) (QuotientGroup.kerLift_injective δ)
  have htop : δ.ker = ⊤ := eq_top_of_isPGroup_quotient hSker hS.2.2 hP
  intro h hh
  have hmem : (⟨h, hh⟩ : ↥H) ∈ δ.ker := by rw [htop]; trivial
  rw [MonoidHom.mem_ker] at hmem
  have hxN : QuotientGroup.mk (⟨h * x * h⁻¹ * x⁻¹, hxK' ⟨h, hh⟩⟩ : ↥K) = 1 := hmem
  have := (QuotientGroup.eq_one_iff (⟨h * x * h⁻¹ * x⁻¹, hxK' ⟨h, hh⟩⟩ : ↥K)).mp hxN
  rw [Subgroup.mem_subgroupOf] at this
  simpa using this

theorem _root_.CFSG.Quasithin.F112W.IsChiefSeriesBetween.trans
    {H U : Subgroup G} {M N P : Subgroup G} {a b : ℕ}
    (h₁ : F112W.IsChiefSeriesBetween H U M N a)
    (h₂ : F112W.IsChiefSeriesBetween H U N P b) :
    F112W.IsChiefSeriesBetween H U M P (a + b) := by
  induction h₂ with
  | refl => simpa using h₁
  | central hstep hc _ ih => exact .central hstep hc ih
  | noncentral hstep hnc _ ih =>
    have := F112W.IsChiefSeriesBetween.noncentral hstep hnc ih
    simpa [Nat.add_assoc] using this

theorem commutator_le_of_isChiefSeriesBetween_zero
    {H U S N Hi : Subgroup G} {x : G} {n : ℕ}
    (hS : IsSylowTwoOf S H) (hUH : U ≤ H) (hU : IsElemAbelian 2 U)
    (hN : IsNormalIn H U N) (hHi : IsNormalIn H U Hi) (hNH : N ≤ Hi)
    (hser : F112W.IsChiefSeriesBetween H U N Hi n) (hn : n = 0)
    (hxHi : ∀ h ∈ H, h * x * h⁻¹ * x⁻¹ ∈ Hi)
    (hxS : ∀ s ∈ S, s * x * s⁻¹ * x⁻¹ ∈ N) :
    ∀ h ∈ H, h * x * h⁻¹ * x⁻¹ ∈ N := by
  induction hser with
  | refl => exact hxHi
  | @central Hi' L n hstep hc hs ih =>
    have hL : IsNormalIn H U L := hstep.2.1
    have hNL : N ≤ L := hs.le
    have hxL : ∀ h ∈ H, h * x * h⁻¹ * x⁻¹ ∈ L :=
      commutator_le_of_isCentralStep_of_isSylow hS hUH hU hL hHi
        hstep.2.2.1.le hHi.1 hc hxHi (fun s hs' => hNL (hxS s hs'))
    exact ih hL hNL hn hxL
  | @noncentral Hi' L n hstep hnc hs ih =>
    exact absurd hn (Nat.succ_ne_zero n)

theorem isChiefSeriesBetween_zero_of_isCentralStep {H U N K : Subgroup G}
    (hN : IsNormalIn H U N) (hK : IsNormalIn H U K) (hNK : N ≤ K)
    (hc : IsCentralStep H N K) :
    F112W.IsChiefSeriesBetween H U N K 0 := by
  obtain ⟨n, hser⟩ := F112W.exists_isChiefSeriesBetween hN K hK hNK
  have hn : n = 0 := by
    induction hser with
    | refl => rfl
    | @central K' L n hstep hc' hs ih =>
      have hL : IsNormalIn H U L := hstep.2.1
      have hNL : N ≤ L := hs.le
      have hcL : IsCentralStep H N L := fun g hg x hx => hc g hg x (hstep.2.2.1.le hx)
      exact ih hL hNL hcL
    | @noncentral Hi' L n hstep hnc hs ih =>
      exfalso
      apply hnc
      intro g hg x hx
      exact hs.le (hc g hg x hx)
  rwa [hn] at hser

private theorem map_subgroupOf_conj_normalizer {Hi M : Subgroup G} {h : G}
    (hHi : h ∈ Subgroup.normalizer (Hi : Set G))
    (hM : h ∈ Subgroup.normalizer (M : Set G)) :
    (M.subgroupOf Hi).map (Subgroup.normalizerMonoidHom Hi ⟨h, hHi⟩) = M.subgroupOf Hi := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hzM : (z : G) ∈ M := Subgroup.mem_subgroupOf.mp hz
    have hconjM : h * (z : G) * h⁻¹ ∈ M :=
      (Subgroup.mem_normalizer_iff.mp hM (z : G)).mp hzM
    exact Subgroup.mem_subgroupOf.mpr (by
      change h * (z : G) * h⁻¹ ∈ M
      exact hconjM)
  · intro hy
    have hyM : (y : G) ∈ M := Subgroup.mem_subgroupOf.mp hy
    have hconjM : h⁻¹ * (y : G) * h ∈ M := by
      simpa [inv_inv] using
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hM) (y : G)).mp hyM
    have hconjHi : h⁻¹ * (y : G) * h ∈ Hi := by
      simpa [inv_inv] using
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hHi) (y : G)).mp
          (Subgroup.mem_subgroupOf.mp y.2)
    refine ⟨⟨h⁻¹ * (y : G) * h, hconjHi⟩, ?_, ?_⟩
    · show (⟨h⁻¹ * (y : G) * h, hconjHi⟩ : ↥Hi) ∈ M.subgroupOf Hi
      rw [Subgroup.mem_subgroupOf]
      exact hconjM
    · apply Subtype.ext
      change h * (h⁻¹ * (y : G) * h) * h⁻¹ = (y : G)
      group

private theorem pow_eq_self_of_odd_of_sq {M : Type*} [Monoid M] {a : M} (ha : a * a = 1)
    {o : ℕ} (ho : Odd o) : a ^ o = a := by
  obtain ⟨k, hk⟩ := ho
  rw [hk, pow_succ, pow_mul, show a ^ 2 = 1 by rw [pow_two]; exact ha, one_pow, one_mul]

theorem exists_fixed_norm
    {Q : Type*} [CommGroup Q] {H : Type*} [Group H] [Finite H]
    (act : H →* MulAut Q) {S : Subgroup H} (hodd : ¬ 2 ∣ S.index)
    {v : Q} (hv2 : v * v = 1) (hvS : ∀ s ∈ S, act s v = v)
    {N : Subgroup Q} [N.Normal] (hNinv : ∀ h : H, ∀ x ∈ N, act h x ∈ N)
    (hvN : ∀ h : H, act h v * v⁻¹ ∈ N) :
    ∃ y : Q, (∀ h : H, act h y = y) ∧ y * v⁻¹ ∈ N := by
  classical
  haveI : Fintype (H ⧸ S) := Fintype.ofFinite _
  let F : (H ⧸ S) → Q := fun q =>
    Quotient.liftOn' q (fun h : H => act h v)
      (by
        intro a b hab
        have hab' : a⁻¹ * b ∈ S := QuotientGroup.leftRel_apply.mp hab
        have h : act (a⁻¹ * b) v = v := hvS (a⁻¹ * b) hab'
        have e : a * (a⁻¹ * b) = b := by group
        exact (calc act b v = act (a * (a⁻¹ * b)) v := by rw [e]
          _ = act a (act (a⁻¹ * b) v) := by rw [map_mul, MulAut.mul_apply]
          _ = act a v := by rw [h]).symm)
  have hFmk : ∀ h : H, F (QuotientGroup.mk h) = act h v := fun h => rfl
  have hF : ∀ (h : H) (q : H ⧸ S), act h (F q) = F (h • q) := by
    intro h q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hFmk, show (h • QuotientGroup.mk a : H ⧸ S) = QuotientGroup.mk (h * a) from rfl,
      hFmk, map_mul, MulAut.mul_apply]
  let y : Q := ∏ q, F q
  have hyfix : ∀ h : H, act h y = y := by
    intro h
    change act h (∏ q, F q) = ∏ q, F q
    rw [map_prod]
    rw [Finset.prod_congr rfl fun q _ => hF h q]
    exact Fintype.prod_equiv (MulAction.toPerm h) _ _ (fun q => rfl)
  have hterm : ∀ q : H ⧸ S, F q * v⁻¹ ∈ N := by
    intro q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hFmk]
    exact hvN h
  have hcard : Fintype.card (H ⧸ S) = S.index := by
    rw [← Nat.card_eq_fintype_card]; rfl
  have hodd' : Odd (Fintype.card (H ⧸ S)) := by
    rw [hcard]
    exact Nat.coprime_two_left.mp ((Nat.prime_two.coprime_iff_not_dvd).mpr hodd)
  have hv2inv : v⁻¹ * v⁻¹ = 1 := by
    rw [← mul_inv_rev, hv2, inv_one]
  have hprod : y * v⁻¹ = ∏ q : H ⧸ S, (F q * v⁻¹) := by
    change (∏ q, F q) * v⁻¹ = ∏ q, (F q * v⁻¹)
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_const, Finset.card_univ]
    exact (pow_eq_self_of_odd_of_sq hv2inv hodd').symm
  refine ⟨y, hyfix, ?_⟩
  rw [hprod]
  exact Subgroup.prod_mem N (fun q _ => hterm q)

theorem conj_action_hom {Hi M H : Subgroup G}
    (hHiNorm : H ≤ Subgroup.normalizer (Hi : Set G))
    (hMNorm : H ≤ Subgroup.normalizer (M : Set G))
    [hN : (M.subgroupOf Hi).Normal] :
    ∃ act : H →* MulAut (Hi ⧸ M.subgroupOf Hi),
      ∀ (h : H) (y : ↥Hi),
        act h (QuotientGroup.mk y) =
          QuotientGroup.mk (Subgroup.normalizerMonoidHom Hi ⟨h, hHiNorm h.2⟩ y) := by
  classical
  let conjHi (h : H) : MulAut ↥Hi :=
    Subgroup.normalizerMonoidHom Hi ⟨h, hHiNorm h.2⟩
  let act (h : H) : MulAut (Hi ⧸ M.subgroupOf Hi) :=
    QuotientGroup.congr (M.subgroupOf Hi) (M.subgroupOf Hi) (conjHi h)
      (map_subgroupOf_conj_normalizer (hHiNorm h.2) (hMNorm h.2))
  have hact_mk : ∀ (h : H) (y : ↥Hi),
      act h (QuotientGroup.mk y) = QuotientGroup.mk (conjHi h y) := by
    intro h y
    exact QuotientGroup.congr_mk (M.subgroupOf Hi) (M.subgroupOf Hi) (conjHi h) _ y
  refine ⟨{ toFun := act, map_one' := ?_, map_mul' := ?_ }, hact_mk⟩
  · ext q
    induction q using QuotientGroup.induction_on with
    | H y =>
      rw [hact_mk]
      simp only [conjHi]
      have e : (⟨1, hHiNorm H.one_mem⟩ : Subgroup.normalizer (Hi : Set G)) = 1 := by
        ext; rfl
      have h1 : (Subgroup.normalizerMonoidHom Hi ⟨1, hHiNorm H.one_mem⟩) y = y := by
        rw [e, map_one, MulAut.one_apply]
      simp only [Subgroup.coe_one]
      rw [h1]
      rfl
  · intro h1 h2
    ext q
    induction q using QuotientGroup.induction_on with
    | H y =>
      rw [hact_mk, MulAut.mul_apply, hact_mk, hact_mk]
      simp only [conjHi]
      have e : (⟨↑(h1 * h2), hHiNorm (H.mul_mem h1.2 h2.2)⟩ :
          Subgroup.normalizer (Hi : Set G)) =
          ⟨↑h1, hHiNorm h1.2⟩ * ⟨↑h2, hHiNorm h2.2⟩ := by
        ext
        change ((h1 * h2 : H) : G) = (h1 : G) * (h2 : G)
        rfl
      have h1 : (Subgroup.normalizerMonoidHom Hi
          ⟨↑(h1 * h2), hHiNorm (H.mul_mem h1.2 h2.2)⟩) y =
          (Subgroup.normalizerMonoidHom Hi ⟨↑h1, hHiNorm h1.2⟩)
            ((Subgroup.normalizerMonoidHom Hi ⟨↑h2, hHiNorm h2.2⟩) y) := by
        rw [e, map_mul, MulAut.mul_apply]
      rw [h1]

private theorem prod_range_shift {M : Type*} [CommGroup M] (f : ℕ → M) {o : ℕ}
    (h : f o = f 0) :
    (∏ j ∈ Finset.range o, f (j+1)) = ∏ j ∈ Finset.range o, f j := by
  have h1 := Finset.prod_range_succ' f o
  have h2 := Finset.prod_range_succ f o
  rw [h2, h] at h1
  exact (mul_right_cancel h1).symm

theorem mem_of_comm_mem_of_fixedPointFree {Y Lo L : Subgroup G} {d y : G}
    (hY2 : ∀ z ∈ Y, z * z = 1)
    (hYab : ∀ z ∈ Y, ∀ w ∈ Y, z * w = w * z)
    (hLoL : Lo ≤ L) (hy : y ∈ Y)
    (hdY : ∀ z ∈ Y, d * z * d⁻¹ ∈ Y)
    (hdL : ∀ z ∈ L, d * z * d⁻¹ ∈ L)
    (hodd : Odd (orderOf d))
    (hfpf : ∀ z ∈ Y, d * z * d⁻¹ * z⁻¹ ∈ Lo → z ∈ Lo)
    (hcomm : d * y * d⁻¹ * y⁻¹ ∈ L) :
    y ∈ L := by
  classical
  letI : CommGroup ↥Y :=
    { (inferInstance : Group ↥Y) with
      mul_comm := fun a b => Subtype.ext (hYab _ a.2 _ b.2) }
  set o := orderOf d with ho
  have hdo : d ^ o = 1 := pow_orderOf_eq_one d
  have hfY : ∀ j : ℕ, d ^ j * y * (d ^ j)⁻¹ ∈ Y := by
    intro j
    induction j with
    | zero => simpa using hy
    | succ j ih =>
      have h := hdY _ ih
      simpa [show d ^ (j+1) * y * (d ^ (j+1))⁻¹ =
          d * (d ^ j * y * (d ^ j)⁻¹) * d⁻¹ by group] using h
  let f : ℕ → ↥Y := fun j => ⟨d ^ j * y * (d ^ j)⁻¹, hfY j⟩
  let wY : ↥Y := ∏ j ∈ Finset.range o, f j
  let w : G := wY
  have hdN : d ∈ Subgroup.normalizer (Y : Set G) :=
    CFSG.GroupTheory.WielandtProduct.mem_normalizer_of_forall_conj_mem hdY
  let φ : MulAut ↥Y := Subgroup.normalizerMonoidHom Y ⟨d, hdN⟩
  have hφ : ∀ j : ℕ, φ (f j) = f (j+1) := by
    intro j
    apply Subtype.ext
    change d * (d ^ j * y * (d ^ j)⁻¹) * d⁻¹ = d ^ (j+1) * y * (d ^ (j+1))⁻¹
    group
  have hf0 : f o = f 0 := by
    apply Subtype.ext
    simp [f, hdo]
  have hφw : φ wY = wY := by
    change φ (∏ j ∈ Finset.range o, f j) = ∏ j ∈ Finset.range o, f j
    rw [map_prod]
    rw [Finset.prod_congr rfl fun j _ => hφ j, prod_range_shift f hf0]
  have hconj : d * w * d⁻¹ = w := by
    have hcoe : ((φ wY : ↥Y) : G) = d * (wY : G) * d⁻¹ := rfl
    rw [← hcoe, hφw]
  have hfjL : ∀ j : ℕ, d ^ j * y * (d ^ j)⁻¹ * y⁻¹ ∈ L := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 : d * (d ^ j * y * (d ^ j)⁻¹ * y⁻¹) * d⁻¹ ∈ L := hdL _ ih
      have h2 : d * y * d⁻¹ * y⁻¹ ∈ L := hcomm
      have e : d ^ (j+1) * y * (d ^ (j+1))⁻¹ * y⁻¹ =
          (d * (d ^ j * y * (d ^ j)⁻¹ * y⁻¹) * d⁻¹) * (d * y * d⁻¹ * y⁻¹) := by
        group
      rw [e]
      exact L.mul_mem h1 h2
  have hyY : (⟨y, hy⟩ : ↥Y) * ⟨y, hy⟩ = 1 := by
    apply Subtype.ext
    simpa using hY2 y hy
  have hyinvY : (⟨y, hy⟩ : ↥Y)⁻¹ * ⟨y, hy⟩⁻¹ = 1 := by
    rw [← mul_inv_rev, hyY, inv_one]
  have hprodY : wY * (⟨y, hy⟩ : ↥Y)⁻¹ =
      ∏ j ∈ Finset.range o, (f j * (⟨y, hy⟩ : ↥Y)⁻¹) := by
    change (∏ j ∈ Finset.range o, f j) * (⟨y, hy⟩ : ↥Y)⁻¹ =
      ∏ j ∈ Finset.range o, (f j * (⟨y, hy⟩ : ↥Y)⁻¹)
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_const, Finset.card_range]
    exact (pow_eq_self_of_odd_of_sq hyinvY hodd).symm
  have hprodL : w * y⁻¹ ∈ L := by
    have hterm : ∀ j ∈ Finset.range o, (f j * (⟨y, hy⟩ : ↥Y)⁻¹ : ↥Y) ∈ L.subgroupOf Y := by
      intro j _
      rw [Subgroup.mem_subgroupOf]
      simpa [f] using hfjL j
    have hmemY : (∏ j ∈ Finset.range o, (f j * (⟨y, hy⟩ : ↥Y)⁻¹ : ↥Y)) ∈ L.subgroupOf Y :=
      Subgroup.prod_mem (L.subgroupOf Y) hterm
    have hmem : ((wY * (⟨y, hy⟩ : ↥Y)⁻¹ : ↥Y) : G) ∈ L := by
      rw [hprodY]
      exact hmemY
    simpa [w, wY] using hmem
  have hwLo : w ∈ Lo := by
    apply hfpf w (by simpa [w] using wY.2)
    have : d * w * d⁻¹ * w⁻¹ = 1 := by rw [hconj]; group
    rw [this]
    exact Lo.one_mem
  have hwL : w ∈ L := hLoL hwLo
  have hyinv : y⁻¹ ∈ L := by
    have := L.mul_mem (L.inv_mem hwL) hprodL
    simpa [mul_assoc] using this
  simpa using L.inv_mem hyinv

theorem exists_fixed_mod_of_isSylow
    {H S U M N Hi : Subgroup G} {x : G}
    (hU : IsElemAbelian 2 U) (hUH : U ≤ H)
    (hHiU : Hi ≤ U) (hMHi : M ≤ Hi) (hNHi : N ≤ Hi) (hMN : M ≤ N)
    (hHHi : H ≤ Subgroup.normalizer (Hi : Set G))
    (hHM : H ≤ Subgroup.normalizer (M : Set G))
    (hHN : H ≤ Subgroup.normalizer (N : Set G))
    (hS : IsSylowTwoOf S H)
    (hxHi : x ∈ Hi)
    (hxS : ∀ s ∈ S, s * x * s⁻¹ * x⁻¹ ∈ M)
    (hxH : ∀ h ∈ H, h * x * h⁻¹ * x⁻¹ ∈ N) :
    ∃ y ∈ Hi, (∀ h ∈ H, h * y * h⁻¹ * y⁻¹ ∈ M) ∧ y * x⁻¹ ∈ N := by
  classical
  have hHiH : Hi ≤ H := hHiU.trans hUH
  letI : CommGroup ↥Hi :=
    { (inferInstance : Group ↥Hi) with
      mul_comm := fun a b => Subtype.ext (by
        simpa using congrArg (Subtype.val)
          (hU.1.is_comm.comm ⟨a.1, hHiU a.2⟩ ⟨b.1, hHiU b.2⟩)) }
  have hMHiNorm : (M.subgroupOf Hi).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hHiH.trans hHM)
  let Q := Hi ⧸ M.subgroupOf Hi
  let act : H →* MulAut Q := (conj_action_hom hHHi hHM).choose
  have hact : ∀ (h : H) (z : ↥Hi),
      act h (QuotientGroup.mk z) =
        QuotientGroup.mk (Subgroup.normalizerMonoidHom Hi ⟨h, hHHi h.2⟩ z) :=
    (conj_action_hom hHHi hHM).choose_spec
  let xHi : ↥Hi := ⟨x, hxHi⟩
  let v : Q := QuotientGroup.mk xHi
  let NQ : Subgroup Q := (N.subgroupOf Hi).map (QuotientGroup.mk' (M.subgroupOf Hi))
  have hNHiNorm : (N.subgroupOf Hi).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hHiH.trans hHN)
  have hNQnorm : NQ.Normal :=
    hNHiNorm.map (QuotientGroup.mk' (M.subgroupOf Hi)) (QuotientGroup.mk'_surjective _)
  have hv2 : v * v = 1 := by
    change QuotientGroup.mk (xHi * xHi) = 1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    change x * x ∈ M
    have hx2 : x * x = 1 := by simpa [pow_two] using hU.2 x (hHiU hxHi)
    rw [hx2]
    exact M.one_mem
  have hvS : ∀ s ∈ S.subgroupOf H, act s v = v := by
    intro s hs
    have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.mp hs
    rw [show v = QuotientGroup.mk xHi from rfl, hact]
    apply QuotientGroup.eq.mpr
    rw [Subgroup.mem_subgroupOf]
    change ((s : G) * x * (s : G)⁻¹)⁻¹ * x ∈ M
    have hk : (s : G) * x * (s : G)⁻¹ = ((s : G) * x * (s : G)⁻¹ * x⁻¹) * x := by group
    rw [hk]
    have e : (((s : G) * x * (s : G)⁻¹ * x⁻¹) * x)⁻¹ * x =
        x⁻¹ * ((s : G) * x * (s : G)⁻¹ * x⁻¹)⁻¹ * x := by group
    rw [e]
    simpa [inv_inv] using
      (Subgroup.mem_normalizer_iff.mp (hHM (H.inv_mem (hHiH hxHi))) _).mp
        (M.inv_mem (hxS (s : G) hsS))
  have hNQinv : ∀ h : H, ∀ z ∈ NQ, act h z ∈ NQ := by
    intro h z hz
    change z ∈ (N.subgroupOf Hi).map (QuotientGroup.mk' (M.subgroupOf Hi)) at hz
    rw [Subgroup.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    change act h (QuotientGroup.mk w) ∈ NQ
    rw [hact]
    refine Subgroup.mem_map.mpr ⟨Subgroup.normalizerMonoidHom Hi ⟨h, hHHi h.2⟩ w, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hw ⊢
    change h * (w : G) * h⁻¹ ∈ N
    exact (Subgroup.mem_normalizer_iff.mp (hHN h.2) (w : G)).mp hw
  have hvN : ∀ h : H, act h v * v⁻¹ ∈ NQ := by
    intro h
    rw [show v = QuotientGroup.mk xHi from rfl, hact]
    change QuotientGroup.mk (Subgroup.normalizerMonoidHom Hi ⟨h, hHHi h.2⟩ xHi) *
      (QuotientGroup.mk xHi : Q)⁻¹ ∈ NQ
    have hmemHi : (h : G) * x * (h : G)⁻¹ * x⁻¹ ∈ Hi := by
      refine Hi.mul_mem ?_ (Hi.inv_mem hxHi)
      exact (Subgroup.mem_normalizer_iff.mp (hHHi h.2) x).mp hxHi
    have hmemN : (h : G) * x * (h : G)⁻¹ * x⁻¹ ∈ N := hxH h h.2
    have hEq : QuotientGroup.mk (Subgroup.normalizerMonoidHom Hi ⟨h, hHHi h.2⟩ xHi) *
        (QuotientGroup.mk xHi : Q)⁻¹ =
        QuotientGroup.mk (⟨(h : G) * x * (h : G)⁻¹ * x⁻¹, hmemHi⟩ : ↥Hi) := by
      rw [show (QuotientGroup.mk xHi : Q)⁻¹ = QuotientGroup.mk xHi⁻¹ from
        (QuotientGroup.mk_inv (N := M.subgroupOf Hi) xHi).symm]
      rw [← QuotientGroup.mk_mul]
      congr 1
    rw [hEq]
    exact Subgroup.mem_map.mpr ⟨⟨_, hmemHi⟩, Subgroup.mem_subgroupOf.mpr hmemN, rfl⟩
  haveI : NQ.Normal := hNQnorm
  obtain ⟨z, hzfix, hzN⟩ : ∃ z : Q, (∀ h : H, act h z = z) ∧ z * v⁻¹ ∈ NQ :=
    exists_fixed_norm act (S := S.subgroupOf H) hS.2.2 hv2 hvS hNQinv hvN
  obtain ⟨yHi, hyz⟩ := QuotientGroup.mk_surjective z
  refine ⟨yHi, yHi.2, ?_, ?_⟩
  · intro h hh
    have h1 : act ⟨h, hh⟩ z = z := hzfix ⟨h, hh⟩
    rw [← hyz] at h1
    rw [hact] at h1
    let A : ↥Hi := Subgroup.normalizerMonoidHom Hi ⟨h, hHHi hh⟩ yHi
    have h1' : QuotientGroup.mk A = QuotientGroup.mk yHi := h1
    have h2 : A⁻¹ * yHi ∈ M.subgroupOf Hi := QuotientGroup.eq.mp h1'
    rw [Subgroup.mem_subgroupOf] at h2
    have hA2 : A * A = 1 := by
      apply Subtype.ext
      have hAHi : (A : G) ∈ Hi := A.2
      simpa [pow_two] using hU.2 (A : G) (hHiU hAHi)
    have hy2 : yHi * yHi = 1 := by
      apply Subtype.ext
      simpa [pow_two] using hU.2 (yHi : G) (hHiU yHi.2)
    have hAinv : A⁻¹ = A := inv_eq_of_mul_eq_one_right hA2
    have hyinv : yHi⁻¹ = yHi := inv_eq_of_mul_eq_one_right hy2
    have h2'' : ((A : G) * (yHi : G)) ∈ M := by
      simpa [hAinv] using h2
    have hyinvG : (yHi : G)⁻¹ = (yHi : G) := by
      simpa using congrArg Subtype.val hyinv
    have h2' : ((A : G) * (yHi : G)⁻¹) ∈ M := by
      rw [hyinvG]
      exact h2''
    exact h2'
  · have h1 : z * v⁻¹ ∈ NQ := hzN
    change z * v⁻¹ ∈ (N.subgroupOf Hi).map (QuotientGroup.mk' (M.subgroupOf Hi)) at h1
    obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp h1
    rw [Subgroup.mem_subgroupOf] at hw
    have hxinvHi : x⁻¹ ∈ Hi := Hi.inv_mem hxHi
    have hyxHi : (yHi : G) * x⁻¹ ∈ Hi := Hi.mul_mem yHi.2 hxinvHi
    have h2 : (QuotientGroup.mk (⟨(yHi : G) * x⁻¹, hyxHi⟩ : ↥Hi) : Q) =
        (QuotientGroup.mk w : Q) := by
      rw [show (QuotientGroup.mk (⟨(yHi : G) * x⁻¹, hyxHi⟩ : ↥Hi) : Q) =
          (QuotientGroup.mk yHi : Q) * (QuotientGroup.mk xHi : Q)⁻¹ from by
        rw [show (QuotientGroup.mk xHi : Q)⁻¹ = QuotientGroup.mk xHi⁻¹ from
          (QuotientGroup.mk_inv (N := M.subgroupOf Hi) xHi).symm]
        rw [← QuotientGroup.mk_mul]
        rfl]
      rw [hyz, ← hwz]
      rfl
    have h3 : ((yHi : G) * x⁻¹)⁻¹ * (w : G) ∈ M := by
      have := QuotientGroup.eq.mp h2
      rw [Subgroup.mem_subgroupOf] at this
      simpa using this
    have h4 : ((yHi : G) * x⁻¹) * (w : G)⁻¹ ∈ M := by
      have h5 : (w : G)⁻¹ * ((yHi : G) * x⁻¹) ∈ M := by
        simpa using M.inv_mem h3
      have hyxH : (yHi : G) * x⁻¹ ∈ H := hHiH (hyxHi)
      have := (Subgroup.mem_normalizer_iff.mp (hHM hyxH) _).mp h5
      simpa [mul_assoc] using this
    have h6 : (yHi : G) * x⁻¹ = (((yHi : G) * x⁻¹) * (w : G)⁻¹) * (w : G) := by group
    rw [h6]
    exact N.mul_mem (hMN h4) hw

theorem isChiefSeriesBetween_zero_of_gen_fixed
    {H S U Lo Hi X : Subgroup G}
    (hS : IsSylowTwoOf S H) (hU : IsElemAbelian 2 U) (hUH : U ≤ H)
    (hHU : H ≤ Subgroup.normalizer (U : Set G))
    (hLo : IsNormalIn H U Lo) (hHi : IsNormalIn H U Hi) (hLoHi : Lo ≤ Hi)
    (hfix : ∀ Lo' Hi' : Subgroup G, Lo ≤ Lo' → Hi' ≤ Hi → IsChiefStep H U Lo' Hi' →
      ¬ IsCentralStep H Lo' Hi' → ∀ x ∈ Hi',
        (∀ n ∈ H ⊓ Subgroup.normalizer (S : Set G), n * x * n⁻¹ * x⁻¹ ∈ Lo') → x ∈ Lo')
    (hX : ∀ n ∈ H ⊓ Subgroup.normalizer (S : Set G), ∀ x ∈ X, n * x * n⁻¹ * x⁻¹ ∈ Lo)
    (hgen : Hi = Lo ⊔ conjClosure X H) :
    F112W.IsChiefSeriesBetween H U Lo Hi 0 := by
  classical
  by_contra hzero
  let P : Subgroup G → Prop := fun K =>
    IsNormalIn H U K ∧ Lo ≤ K ∧ K ≤ Hi ∧ ¬ F112W.IsChiefSeriesBetween H U K Hi 0
  have hPfin : Set.Finite {K : Subgroup G | P K} := Set.toFinite _
  have hPnon : ({K : Subgroup G | P K}).Nonempty := ⟨Lo, hLo, le_rfl, hLoHi, hzero⟩
  obtain ⟨M, hMP, hMmax⟩ := hPfin.exists_maximal hPnon
  obtain ⟨hMnorm, hLoM, hMHi, hMnotzero⟩ := hMP
  have hMltHi : M < Hi := by
    refine lt_of_le_of_ne hMHi ?_
    intro hEq
    apply hMnotzero
    subst hEq
    exact .refl
  let Q : Subgroup G → Prop := fun N => IsNormalIn H U N ∧ M < N ∧ N ≤ Hi
  have hQfin : Set.Finite {N : Subgroup G | Q N} := Set.toFinite _
  have hQnon : ({N : Subgroup G | Q N}).Nonempty := ⟨Hi, hHi, hMltHi, le_rfl⟩
  obtain ⟨N, hNQ, hNmin⟩ := hQfin.exists_minimal hQnon
  obtain ⟨hNnorm, hMN, hNHi⟩ := hNQ
  have hstepMN : IsChiefStep H U M N := by
    refine ⟨hNnorm, hMnorm, hMN, ?_⟩
    intro K hK hMK hKN
    by_cases hKM : K = M
    · exact Or.inl hKM
    · have hMK' : M < K := lt_of_le_of_ne hMK (Ne.symm hKM)
      have hQK : Q K := ⟨hK, hMK', hKN.trans hNHi⟩
      have hNK : N ≤ K := hNmin hQK hKN
      exact Or.inr (le_antisymm hKN hNK)
  have hNzero : F112W.IsChiefSeriesBetween H U N Hi 0 := by
    by_contra h
    have hNP : P N := ⟨hNnorm, hLoM.trans hMN.le, hNHi, h⟩
    have hNM : N ≤ M := hMmax hNP hMN.le
    exact hMN.ne' (le_antisymm hNM hMN.le)
  have hnc : ¬ IsCentralStep H M N := by
    intro hc
    have hMNzero : F112W.IsChiefSeriesBetween H U M N 0 := .central hstepMN hc .refl
    exact hMnotzero (hMNzero.trans hNzero)
  have hfixMN : ∀ x ∈ N,
      (∀ n ∈ H ⊓ Subgroup.normalizer (S : Set G), n * x * n⁻¹ * x⁻¹ ∈ M) → x ∈ M :=
    hfix M N hLoM hNHi hstepMN hnc
  have hXHi : X ≤ Hi := by
    rw [hgen]
    exact (le_conjClosure X H).trans le_sup_right
  have hXnotN : ∃ x ∈ X, x ∉ N := by
    by_contra h
    push Not at h
    have hXM : X ≤ M := by
      intro z hz
      exact hfixMN z (h z hz) (fun n hn => hLoM (hX n hn z hz))
    have hconjM : conjClosure X H ≤ M := by
      apply conjClosure_le
      intro hh hhH z hz
      exact hMnorm.2 hh hhH z (hXM hz)
    have : Hi ≤ M := by
      rw [hgen]
      exact sup_le hLoM hconjM
    exact hMltHi.ne (le_antisymm hMHi this)
  obtain ⟨x, hxX, hxN⟩ := hXnotN
  have hxfixM : ∀ n ∈ H ⊓ Subgroup.normalizer (S : Set G), n * x * n⁻¹ * x⁻¹ ∈ M :=
    fun n hn => hLoM (hX n hn x hxX)
  have hxS_M : ∀ s ∈ S, s * x * s⁻¹ * x⁻¹ ∈ M := by
    intro s hs
    exact hxfixM s ⟨hS.1 hs, Subgroup.le_normalizer hs⟩
  have hxHi : ∀ h ∈ H, h * x * h⁻¹ * x⁻¹ ∈ Hi :=
    fun h hh => Hi.mul_mem (hHi.2 h hh x (hXHi hxX)) (Hi.inv_mem (hXHi hxX))
  have hxN' : ∀ h ∈ H, h * x * h⁻¹ * x⁻¹ ∈ N :=
    commutator_le_of_isChiefSeriesBetween_zero hS hUH hU hNnorm hHi hNHi hNzero rfl hxHi
      (fun s hs => hMN.le (hxS_M s hs))
  obtain ⟨y, hyHi, hyfixM, hyN⟩ :=
    exists_fixed_mod_of_isSylow (M := M) (N := N) (Hi := Hi) (H := H) (S := S) (U := U)
      (x := x) hU hUH hHi.1 (hMN.le.trans hNHi) hNHi hMN.le
      (D14.le_normalizer_of_isNormalIn (H := H) (U := U) hHi)
      (D14.le_normalizer_of_isNormalIn (H := H) (U := U) hMnorm)
      (D14.le_normalizer_of_isNormalIn (H := H) (U := U) hNnorm)
      hS (hXHi hxX) hxS_M hxN'
  have hyNotN : y ∉ N := by
    intro hyN'
    have hxinv : x⁻¹ ∈ N := by
      have := N.mul_mem (N.inv_mem hyN') hyN
      simpa using this
    have hxN'' : x ∈ N := by simpa [inv_inv] using N.inv_mem hxinv
    exact hxN hxN''
  let K : Subgroup G := M ⊔ Subgroup.zpowers y
  have hMK : M < K := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro hEq
    have hyK : y ∈ K := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    have hyM : y ∈ M := hEq ▸ hyK
    exact hyNotN (hMN.le hyM)
  have hKHi : K ≤ Hi := by
    refine sup_le hMHi ?_
    rw [Subgroup.zpowers_le]
    exact hyHi
  have hcentMK : IsCentralStep H M K := by
    intro h hh k hk
    let Fix : Subgroup G :=
      { carrier := {z | z ∈ H ∧ h * z * h⁻¹ * z⁻¹ ∈ M}
        one_mem' := ⟨H.one_mem, by simp⟩
        mul_mem' := by
          intro a b ha hb
          have ha' : a ∈ H ∧ h * a * h⁻¹ * a⁻¹ ∈ M := ha
          have hb' : b ∈ H ∧ h * b * h⁻¹ * b⁻¹ ∈ M := hb
          rcases ha' with ⟨haH, ha⟩
          rcases hb' with ⟨hbH, hb⟩
          refine ⟨H.mul_mem haH hbH, ?_⟩
          have e : h * (a * b) * h⁻¹ * (a * b)⁻¹ =
              (h * a * h⁻¹ * a⁻¹) * (a * (h * b * h⁻¹ * b⁻¹) * a⁻¹) := by group
          rw [e]
          exact M.mul_mem ha (hMnorm.2 a haH _ hb)
        inv_mem' := by
          intro a ha
          have ha' : a ∈ H ∧ h * a * h⁻¹ * a⁻¹ ∈ M := ha
          rcases ha' with ⟨haH, ha⟩
          refine ⟨H.inv_mem haH, ?_⟩
          have e : h * a⁻¹ * h⁻¹ * (a⁻¹)⁻¹ = a⁻¹ * (h * a * h⁻¹ * a⁻¹)⁻¹ * a := by group
          rw [e]
          simpa [inv_inv] using
            hMnorm.2 a⁻¹ (H.inv_mem haH) _ (M.inv_mem ha) }
    have hMfix : M ≤ Fix := by
      intro m hm
      exact ⟨hUH (hMnorm.1 hm), M.mul_mem (hMnorm.2 h hh m hm) (M.inv_mem hm)⟩
    have hyFix : y ∈ Fix := ⟨hUH (hHi.1 hyHi), hyfixM h hh⟩
    have hFixK : K ≤ Fix := sup_le hMfix (Subgroup.zpowers_le.mpr hyFix)
    exact (hFixK hk).2
  have hHnormK : H ≤ Subgroup.normalizer (K : Set G) := by
    intro h hh
    exact CFSG.GroupTheory.WielandtProduct.mem_normalizer_of_forall_conj_mem
      (H := K) (g := h) (fun k hk => by
        have hc : h * k * h⁻¹ * k⁻¹ ∈ M := hcentMK h hh k hk
        have e : h * k * h⁻¹ = (h * k * h⁻¹ * k⁻¹) * k := by group
        rw [e]
        exact K.mul_mem (Subgroup.mem_sup_left hc) hk)
  have hKnorm : IsNormalIn H U K :=
    ⟨hKHi.trans hHi.1, fun g hg z hz =>
      (Subgroup.mem_normalizer_iff.mp (hHnormK hg) z).mp hz⟩
  have hKzero : F112W.IsChiefSeriesBetween H U K Hi 0 := by
    by_contra h
    have hKP : P K := ⟨hKnorm, hLoM.trans hMK.le, hKHi, h⟩
    have hKM : K ≤ M := hMmax hKP hMK.le
    exact hMK.ne' (le_antisymm hKM hMK.le)
  have hMKzero : F112W.IsChiefSeriesBetween H U M K 0 :=
    isChiefSeriesBetween_zero_of_isCentralStep hMnorm hKnorm le_sup_left hcentMK
  have htrans : F112W.IsChiefSeriesBetween H U M Hi (0 + 0) :=
    hMKzero.trans hKzero
  exact hMnotzero (by simpa using htrans)

end CFSG.Quasithin.Stroth
