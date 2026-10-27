module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SolvableMinimalNormal
public import CFSG.Quasithin.Background.A1cA131
public import CFSG.Quasithin.EmptyFaithful.S14110AuxWreath
public import CFSG.Quasithin.EmptyFaithful.S151bW3Mod

public section

namespace CFSG.Quasithin

open CFSG.Open

section Generic

variable {Y : Type*} [Group Y] [Finite Y]

omit [Finite Y] in
theorem le_pCore_open151b {p : ℕ} {N : Subgroup Y} (hN : N.Normal) (hp : IsPGroup p N) :
    N ≤ CFSG.Open.pCore p Y :=
  le_sSup ⟨hN, hp⟩

theorem exists_normal_pGroup_le151b (hsolv : Group.IsSolvable Y) (N : Subgroup Y) [N.Normal]
    (hN : N ≠ ⊥) :
    ∃ (r : ℕ) (K : Subgroup Y), r.Prime ∧ K.Normal ∧ K ≤ N ∧ K ≠ ⊥ ∧ IsPGroup r K := by
  obtain ⟨M, hMn, hMN, hMne, hMmin⟩ := CFSG.exists_minimal_normal_le N inferInstance hN
  have hminimal : CFSG.RankThreeEvenClassification.Helpers.MinimalNontrivialNormal M :=
    ⟨⟨hMn, hMne⟩, fun K hK hKM => (hMmin K hK.1 hKM hK.2).ge⟩
  have : Group.IsSolvable M := inferInstance
  obtain ⟨r, hr, -, d, -, hcard⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.minimal_normal_solvable_elementary M hminimal
      inferInstance
  have : Fact r.Prime := ⟨hr⟩
  exact ⟨r, M, hr, hMn, hMN, hMne, IsPGroup.of_card hcard⟩

theorem five_le_of_prime_ne151b {r : ℕ} (hr : r.Prime) (h2 : r ≠ 2) (h3 : r ≠ 3) : 5 ≤ r := by
  by_contra h
  push Not at h
  have := hr.two_le
  interval_cases r <;> first | omega | exact absurd hr (by norm_num)

theorem a131Concl_of_solvable151b (hsolv : Group.IsSolvable Y)
    (hO2 : ∀ N : Subgroup Y, N.Normal → IsPGroup 2 N → N = ⊥)
    (hR : ∀ q : ℕ, q.Prime → 5 ≤ q → ∀ N : Subgroup Y, N.Normal → IsPGroup q N → N = ⊥)
    {M : Type} [Group M] [Finite M] (φ : M →* Y) (hφ : Function.Surjective φ)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup M) ≤ 2) : A1c.A131Concl 3 Y := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hpp : CFSG.pPrimeCore 3 Y = ⊥ := by
    refine eq_bot_iff.mpr (sSup_le fun K hK => ?_)
    obtain ⟨hKn, hKc⟩ := hK
    by_contra hne
    have hK1 : K ≠ ⊥ := fun h => hne (h ▸ le_rfl)
    obtain ⟨r, K₀, hr, hK₀n, hK₀K, hK₀ne, hK₀p⟩ := exists_normal_pGroup_le151b hsolv K hK1
    have : Fact r.Prime := ⟨hr⟩
    have hrdvd : r ∣ Nat.card K₀ := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hK₀p
      have hn0 : n ≠ 0 := by
        rintro rfl
        exact hK₀ne (Subgroup.card_eq_one.mp (by simpa using hn))
      rw [hn]
      exact dvd_pow_self r hn0
    have hr3 : r ≠ 3 := by
      rintro rfl
      have h3K : 3 ∣ Nat.card K := hrdvd.trans (Subgroup.card_dvd_of_le hK₀K)
      have := Nat.Coprime.eq_one_of_dvd hKc h3K
      omega
    by_cases hr2 : r = 2
    · subst hr2
      exact hK₀ne (hO2 K₀ hK₀n hK₀p)
    · exact hK₀ne (hR r hr (five_le_of_prime_ne151b hr hr2 hr3) K₀ hK₀n hK₀p)
  have hfit : CFSG.fittingSubgroup Y = CFSG.pCore 3 Y := CFSG.Fitting_eq_pcore Y 3 hpp
  have hcent := CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv
  have hF : Subgroup.centralizer (CFSG.Open.pCore 3 Y : Set Y) ≤ CFSG.Open.pCore 3 Y := by
    rw [← hfit]
    exact hcent
  exact A1c.A131Concl_of_surjective (by norm_num : 3 ≠ 2) hF _ M φ hφ rfl hrk

omit [Finite Y] in
theorem mem_centralizer_zpowers151b {s k : Y} (h : k * s = s * k) :
    k ∈ Subgroup.centralizer (Subgroup.zpowers s : Set Y) := by
  refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  exact (Commute.zpow_left (show Commute s k from h.symm) j).eq

theorem eq_bot_of_centralizer151b (hsolv : Group.IsSolvable Y)
    (hO2 : ∀ N : Subgroup Y, N.Normal → IsPGroup 2 N → N = ⊥)
    (hR : ∀ q : ℕ, q.Prime → 5 ≤ q → ∀ N : Subgroup Y, N.Normal → IsPGroup q N → N = ⊥)
    (hA : A1c.A131Concl 3 Y) {a s : Y} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (hs2 : s ^ 2 = 1)
    (hs1 : s ≠ 1) (has : s * a = a * s) {P : Subgroup Y} (hPn : P.Normal) (hP3 : IsPGroup 3 P)
    (haP : a ∈ P) {C : Subgroup Y} [C.Normal] (hCs : ∀ k ∈ C, k * s = s * k)
    (hCa : ∀ k ∈ C, k ∈ Subgroup.zpowers a → k = 1) : C = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  by_contra hC
  obtain ⟨r, K, hr, hKn, hKC, hKne, hKp⟩ := exists_normal_pGroup_le151b hsolv C hC
  have hr2 : r ≠ 2 := by rintro rfl; exact hKne (hO2 K hKn hKp)
  have hr3 : r = 3 := by
    by_contra h3
    exact hKne (hR r hr (five_le_of_prime_ne151b hr hr2 h3) K hKn hKp)
  subst hr3
  have hs2g : IsPGroup 2 (Subgroup.zpowers s) := isPGroup_zpowers_of_pow_eq_one151b hs2
  have hcyc := hA.1 (Subgroup.zpowers s) hs2g (fun h => hs1 (Subgroup.zpowers_eq_bot.mp h))
  set Z := CFSG.Open.pCore 3 Y ⊓ Subgroup.centralizer (Subgroup.zpowers s : Set Y) with hZ
  have hK3 : 3 ∣ Nat.card K := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hKp
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hKne (Subgroup.card_eq_one.mp (by simpa using hn))
    rw [hn]
    exact dvd_pow_self 3 hn0
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' 3 hK3
  have hk' : orderOf (k : Y) = 3 := by rw [Subgroup.orderOf_coe]; exact hk
  have hkZ : (k : Y) ∈ Z :=
    ⟨le_pCore_open151b hKn hKp k.2, mem_centralizer_zpowers151b (hCs _ (hKC k.2))⟩
  have haZ : a ∈ Z :=
    ⟨le_pCore_open151b hPn hP3 haP, mem_centralizer_zpowers151b has.symm⟩
  have hao : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hle_k : Subgroup.zpowers (k : Y) ≤ Z := Subgroup.zpowers_le.mpr hkZ
  have hle_a : Subgroup.zpowers a ≤ Z := Subgroup.zpowers_le.mpr haZ
  have hHeq : (Subgroup.zpowers (k : Y)).subgroupOf Z = (Subgroup.zpowers a).subgroupOf Z := by
    have := hcyc
    rw [IsCyclic.subgroup_eq_iff_card_eq]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle_k).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle_a).toEquiv, Nat.card_zpowers,
      Nat.card_zpowers, hk', hao]
  have hamem : a ∈ Subgroup.zpowers (k : Y) := by
    have h1 : (⟨a, haZ⟩ : Z) ∈ (Subgroup.zpowers a).subgroupOf Z :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers a)
    rw [← hHeq] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  have haK : a ∈ K := (Subgroup.zpowers_le.mpr k.2) hamem
  exact ha1 (hCa a (hKC haK) (Subgroup.mem_zpowers a))

end Generic


section DihedralThree

open DihedralGroup

theorem dd_x_shape151b :
    ∀ (e₁ e₂ : ZMod 3) (x : DihedralGroup 3 × DihedralGroup 3), e₁ ≠ 0 → e₂ ≠ 0 →
      x * x = 1 → x * (r e₁, 1) * x⁻¹ = (r e₁, 1)⁻¹ → x * (1, r e₂) * x⁻¹ = (1, r e₂) →
      ∃ k : ZMod 3, x = (sr k, 1) := by
  decide

theorem dd_y_shape151b :
    ∀ (e₁ e₂ : ZMod 3) (y : DihedralGroup 3 × DihedralGroup 3), e₁ ≠ 0 → e₂ ≠ 0 →
      y * y = 1 → y * (1, r e₂) * y⁻¹ = (1, r e₂)⁻¹ → y * (r e₁, 1) * y⁻¹ = (r e₁, 1) →
      ∃ l : ZMod 3, y = (1, sr l) := by
  decide

theorem dd_exists_v151b :
    ∀ (e₁ e₂ k l : ZMod 3), e₁ ≠ 0 → e₂ ≠ 0 →
      ∃ v : DihedralGroup 3 × DihedralGroup 3,
        v * (r 1, 1) * v⁻¹ = (r e₁, 1) ∧ v * (1, r 1) * v⁻¹ = (1, r e₂) ∧
        v * (sr 0, 1) * v⁻¹ = (sr k, 1) ∧ v * (1, sr 0) * v⁻¹ = (1, sr l) := by
  decide

theorem dd_normal_form151b :
    ∀ z : DihedralGroup 3 × DihedralGroup 3, ∃ i j : Fin 3, ∃ a b : Fin 2,
      z = ((r 1 : DihedralGroup 3), (1 : DihedralGroup 3)) ^ (i : ℕ) *
        ((1 : DihedralGroup 3), (r 1 : DihedralGroup 3)) ^ (j : ℕ) *
        ((sr 0 : DihedralGroup 3), (1 : DihedralGroup 3)) ^ (a : ℕ) *
        ((1 : DihedralGroup 3), (sr 0 : DihedralGroup 3)) ^ (b : ℕ) := by
  decide

theorem dd_inner151b (f : DihedralGroup 3 × DihedralGroup 3 →* DihedralGroup 3 × DihedralGroup 3)
    {e₁ e₂ : ZMod 3} (he₁ : e₁ ≠ 0) (he₂ : e₂ ≠ 0) (h₁ : f (r 1, 1) = (r e₁, 1))
    (h₂ : f (1, r 1) = (1, r e₂)) :
    ∃ v : DihedralGroup 3 × DihedralGroup 3, ∀ z, f z = v * z * v⁻¹ := by
  have hxx : f (sr 0, 1) * f (sr 0, 1) = 1 := by
    rw [← map_mul]
    have : ((sr 0 : DihedralGroup 3), (1 : DihedralGroup 3)) * (sr 0, 1) = 1 := by decide
    rw [this, map_one]
  have hyy : f (1, sr 0) * f (1, sr 0) = 1 := by
    rw [← map_mul]
    have : ((1 : DihedralGroup 3), (sr 0 : DihedralGroup 3)) * (1, sr 0) = 1 := by decide
    rw [this, map_one]
  have hx₁ : f (sr 0, 1) * (r e₁, 1) * (f (sr 0, 1))⁻¹ = (r e₁, 1)⁻¹ := by
    have e : ((sr 0 : DihedralGroup 3), (1 : DihedralGroup 3)) * (r 1, 1) * (sr 0, 1)⁻¹ =
        ((r 1 : DihedralGroup 3), (1 : DihedralGroup 3))⁻¹ := by decide
    have := congrArg f e
    rwa [map_mul, map_mul, map_inv, map_inv, h₁] at this
  have hx₂ : f (sr 0, 1) * (1, r e₂) * (f (sr 0, 1))⁻¹ = (1, r e₂) := by
    have e : ((sr 0 : DihedralGroup 3), (1 : DihedralGroup 3)) * (1, r 1) * (sr 0, 1)⁻¹ =
        ((1 : DihedralGroup 3), (r 1 : DihedralGroup 3)) := by decide
    have := congrArg f e
    rwa [map_mul, map_mul, map_inv, h₂] at this
  have hy₂ : f (1, sr 0) * (1, r e₂) * (f (1, sr 0))⁻¹ = (1, r e₂)⁻¹ := by
    have e : ((1 : DihedralGroup 3), (sr 0 : DihedralGroup 3)) * (1, r 1) * (1, sr 0)⁻¹ =
        ((1 : DihedralGroup 3), (r 1 : DihedralGroup 3))⁻¹ := by decide
    have := congrArg f e
    rwa [map_mul, map_mul, map_inv, map_inv, h₂] at this
  have hy₁ : f (1, sr 0) * (r e₁, 1) * (f (1, sr 0))⁻¹ = (r e₁, 1) := by
    have e : ((1 : DihedralGroup 3), (sr 0 : DihedralGroup 3)) * (r 1, 1) * (1, sr 0)⁻¹ =
        ((r 1 : DihedralGroup 3), (1 : DihedralGroup 3)) := by decide
    have := congrArg f e
    rwa [map_mul, map_mul, map_inv, h₁] at this
  obtain ⟨k, hk⟩ := dd_x_shape151b e₁ e₂ (f (sr 0, 1)) he₁ he₂ hxx hx₁ hx₂
  obtain ⟨l, hl⟩ := dd_y_shape151b e₁ e₂ (f (1, sr 0)) he₁ he₂ hyy hy₂ hy₁
  obtain ⟨v, hv1, hv2, hv3, hv4⟩ := dd_exists_v151b e₁ e₂ k l he₁ he₂
  refine ⟨v, fun z => ?_⟩
  obtain ⟨i, j, a, b, rfl⟩ := dd_normal_form151b z
  have c1 : MulAut.conj v ((r 1 : DihedralGroup 3), (1 : DihedralGroup 3)) = (r e₁, 1) := by
    rw [MulAut.conj_apply]; exact hv1
  have c2 : MulAut.conj v ((1 : DihedralGroup 3), (r 1 : DihedralGroup 3)) = (1, r e₂) := by
    rw [MulAut.conj_apply]; exact hv2
  have c3 : MulAut.conj v ((sr 0 : DihedralGroup 3), (1 : DihedralGroup 3)) = (sr k, 1) := by
    rw [MulAut.conj_apply]; exact hv3
  have c4 : MulAut.conj v ((1 : DihedralGroup 3), (sr 0 : DihedralGroup 3)) = (1, sr l) := by
    rw [MulAut.conj_apply]; exact hv4
  rw [← MulAut.conj_apply]
  simp only [map_mul, map_pow]
  rw [h₁, h₂, hk, hl, c1, c2, c3, c4]

def dihToPerm3151b : DihedralGroup 3 →* Equiv.Perm (Fin 3) where
  toFun x := match x with
    | r i => Equiv.addRight i
    | sr i => Equiv.subLeft (-i)
  map_one' := by decide
  map_mul' := by decide

theorem dihToPerm3151b_bijective : Function.Bijective dihToPerm3151b := by decide

noncomputable def dihEquivPerm3151b : DihedralGroup 3 ≃* Equiv.Perm (Fin 3) :=
  MulEquiv.ofBijective dihToPerm3151b dihToPerm3151b_bijective

end DihedralThree

namespace SixData151b

section Assembly

variable {W : Type*} [CommGroup W] [Finite W]

theorem mem_sup_of_typeI (S : SixData151b W 3) (hW : ∀ w : W, w ^ 2 = 1)
    {X : Subgroup (MulAut W)} (hA₁X : S.A₁ ≤ X) (hA₂X : S.A₂ ≤ X)
    (hnorm : ∀ g ∈ X, ∀ z ∈ S.A₁ ⊔ S.A₂, g * z * g⁻¹ ∈ S.A₁ ⊔ S.A₂)
    (hC : ∀ c ∈ X, (∀ z ∈ S.A₁ ⊔ S.A₂, c * z = z * c) → c = 1) {g : MulAut W} (hgX : g ∈ X)
    (hI : S.TypeI g) : g ∈ S.A₁ ⊔ S.A₂ := by
  have hp : (3 : ℕ) = 3 ∨ (3 : ℕ) = 5 := Or.inl rfl
  have hg := hnorm g hgX
  obtain ⟨k, k', hk, hk', h1, h2⟩ : ∃ k k' : ZMod 3, k ≠ 0 ∧ k' ≠ 0 ∧
      g * S.a₁ * g⁻¹ = S.ι₁ (DihedralGroup.r k) ∧ g * S.a₂ * g⁻¹ = S.ι₂ (DihedralGroup.r k') := by
    rcases S.typeI_or_typeII_exp hp hW hg with h | ⟨k, k', hk, hk', h1, h2⟩
    · exact h
    · exfalso
      have h3 : g * S.a₁ * g⁻¹ ∈ S.A₁ ⊓ S.A₂ :=
        ⟨Subgroup.zpowers_le.mpr S.a₁_mem hI.1, h1 ▸ S.ι₂_mem _⟩
      rw [S.inf, Subgroup.mem_bot] at h3
      apply S.a₁_ne_one hp
      calc S.a₁ = g⁻¹ * (g * S.a₁ * g⁻¹) * g := by group
        _ = 1 := by rw [h3]; group
  have hg' : ∀ z : DihedralGroup 3 × DihedralGroup 3, ∃ w, S.ι w = g * S.ι z * g⁻¹ := by
    intro z
    have hz : S.ι z ∈ S.A₁ ⊔ S.A₂ := by rw [← S.range_ι]; exact ⟨z, rfl⟩
    have := hg _ hz
    rwa [← S.range_ι] at this
  choose f hf using hg'
  have hfmul : ∀ z z', f (z * z') = f z * f z' := by
    intro z z'
    apply S.ι_injective
    rw [hf, map_mul, map_mul, hf, hf]
    group
  have hfone : f 1 = 1 := by
    apply S.ι_injective
    rw [hf, map_one]
    group
  let F : DihedralGroup 3 × DihedralGroup 3 →* DihedralGroup 3 × DihedralGroup 3 :=
    { toFun := f, map_one' := hfone, map_mul' := hfmul }
  have hF1 : F (DihedralGroup.r 1, 1) = (DihedralGroup.r k, 1) := by
    apply S.ι_injective
    show S.ι (f _) = _
    rw [hf]
    show g * S.a₁ * g⁻¹ = _
    rw [h1, S.ι_inl]
  have hF2 : F (1, DihedralGroup.r 1) = (1, DihedralGroup.r k') := by
    apply S.ι_injective
    show S.ι (f _) = _
    rw [hf]
    show g * S.a₂ * g⁻¹ = _
    rw [h2, S.ι_inr]
  obtain ⟨v, hv⟩ := dd_inner151b F hk hk' hF1 hF2
  have hιvX : S.ι v ∈ X := by
    have : S.ι v ∈ S.A₁ ⊔ S.A₂ := by rw [← S.range_ι]; exact ⟨v, rfl⟩
    exact sup_le hA₁X hA₂X this
  have hcX : (S.ι v)⁻¹ * g ∈ X := X.mul_mem (X.inv_mem hιvX) hgX
  have hc1 : (S.ι v)⁻¹ * g = 1 := by
    apply hC _ hcX
    intro z hz
    rw [← S.range_ι] at hz
    obtain ⟨w, rfl⟩ := hz
    have e : g * S.ι w * g⁻¹ = S.ι v * S.ι w * (S.ι v)⁻¹ := by
      rw [← hf w]
      show S.ι (F w) = _
      rw [hv w, map_mul, map_mul, map_inv]
    calc (S.ι v)⁻¹ * g * S.ι w = (S.ι v)⁻¹ * (g * S.ι w * g⁻¹) * g := by group
      _ = (S.ι v)⁻¹ * (S.ι v * S.ι w * (S.ι v)⁻¹) * g := by rw [e]
      _ = S.ι w * ((S.ι v)⁻¹ * g) := by group
  have hgv : g = S.ι v := by
    have := congrArg (fun c => S.ι v * c) hc1
    simpa using this
  rw [hgv, ← S.range_ι]
  exact ⟨v, rfl⟩

omit [Finite W] in
theorem exists_involution {p : ℕ} (S : SixData151b W p) {w : DihedralGroup p × DihedralGroup p}
    (hw : S.τ * S.τ = S.ι w) :
    ∃ s : MulAut W, s * s = 1 ∧ (∃ x : DihedralGroup p, s = S.τ * S.ι₁ x) ∧
      (∀ a ∈ S.A₁, s * a * s⁻¹ ∈ S.A₂) ∧ (∀ b ∈ S.A₂, s * b * s⁻¹ ∈ S.A₁) := by
  obtain ⟨w₁, w₂⟩ := w
  have hcomm : S.τ * S.ι (w₁, w₂) * S.τ⁻¹ = S.ι (w₁, w₂) := by
    rw [← hw]; group
  obtain ⟨y, hy⟩ := S.exists_ι₂ (S.τ₁₂ _ (S.ι₁_mem w₁))
  obtain ⟨x, hx⟩ := S.exists_ι₁ (S.τ₂₁ _ (S.ι₂_mem w₂))
  have hprod : S.τ * S.ι (w₁, w₂) * S.τ⁻¹ = S.ι₂ y * S.ι₁ x := by
    rw [ι_apply]
    calc S.τ * (S.ι₁ w₁ * S.ι₂ w₂) * S.τ⁻¹
        = (S.τ * S.ι₁ w₁ * S.τ⁻¹) * (S.τ * S.ι₂ w₂ * S.τ⁻¹) := by group
      _ = S.ι₂ y * S.ι₁ x := by rw [← hy, ← hx]
  have hxy : S.ι (x, y) = S.ι (w₁, w₂) := by
    rw [ι_apply, ← hcomm, hprod]
    exact (S.commute_ι x y).eq
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (S.ι_injective hxy)
  have hconj : S.τ * (S.ι₁ x)⁻¹ = (S.ι₂ y)⁻¹ * S.τ := by
    rw [hy]; group
  have hss : S.τ * (S.ι₁ x)⁻¹ * (S.τ * (S.ι₁ x)⁻¹) = 1 := by
    calc S.τ * (S.ι₁ x)⁻¹ * (S.τ * (S.ι₁ x)⁻¹)
        = (S.τ * (S.ι₁ x)⁻¹) * S.τ * (S.ι₁ x)⁻¹ := by group
      _ = (S.ι₂ y)⁻¹ * S.τ * S.τ * (S.ι₁ x)⁻¹ := by rw [hconj]
      _ = (S.ι₂ y)⁻¹ * (S.τ * S.τ) * (S.ι₁ x)⁻¹ := by group
      _ = (S.ι₂ y)⁻¹ * (S.ι₁ x * S.ι₂ y) * (S.ι₁ x)⁻¹ := by rw [hw, ι_apply]
      _ = 1 := by rw [(S.commute_ι x y).eq]; group
  refine ⟨S.τ * (S.ι₁ x)⁻¹, hss, ⟨x⁻¹, by rw [map_inv]⟩, ?_, ?_⟩
  · intro a ha
    have : S.τ * (S.ι₁ x)⁻¹ * a * (S.τ * (S.ι₁ x)⁻¹)⁻¹ =
        S.τ * ((S.ι₁ x)⁻¹ * a * S.ι₁ x) * S.τ⁻¹ := by group
    rw [this]
    exact S.τ₁₂ _ (S.A₁.mul_mem (S.A₁.mul_mem (S.A₁.inv_mem (S.ι₁_mem x)) ha) (S.ι₁_mem x))
  · intro b hb
    have hbx : (S.ι₁ x)⁻¹ * b * S.ι₁ x = b := by
      have := S.comm _ (S.ι₁_mem x) b hb
      calc (S.ι₁ x)⁻¹ * b * S.ι₁ x = (S.ι₁ x)⁻¹ * (b * S.ι₁ x) := by group
        _ = (S.ι₁ x)⁻¹ * (S.ι₁ x * b) := by rw [← this]
        _ = b := by group
    have : S.τ * (S.ι₁ x)⁻¹ * b * (S.τ * (S.ι₁ x)⁻¹)⁻¹ =
        S.τ * ((S.ι₁ x)⁻¹ * b * S.ι₁ x) * S.τ⁻¹ := by group
    rw [this, hbx]
    exact S.τ₂₁ _ hb

theorem nonempty_mulEquiv_wreath3 (S : SixData151b W 3) (hW : ∀ w : W, w ^ 2 = 1)
    {X : Subgroup (MulAut W)} (hA₁X : S.A₁ ≤ X) (hA₂X : S.A₂ ≤ X) (hτX : S.τ ∈ X)
    (hnorm : ∀ g ∈ X, ∀ z ∈ S.A₁ ⊔ S.A₂, g * z * g⁻¹ ∈ S.A₁ ⊔ S.A₂)
    (hC : ∀ c ∈ X, (∀ z ∈ S.A₁ ⊔ S.A₂, c * z = z * c) → c = 1) :
    Nonempty (↥X ≃* Equiv.Perm (Fin 3) ≀ᵣ Multiplicative (ZMod 2)) := by
  have hp : (3 : ℕ) = 3 ∨ (3 : ℕ) = 5 := Or.inl rfl
  have hτ2 : S.TypeII S.τ := S.typeII_of_swap hp hW (hnorm _ hτX) S.τ₁₂
  have hττ : S.τ * S.τ ∈ S.A₁ ⊔ S.A₂ :=
    S.mem_sup_of_typeI hW hA₁X hA₂X hnorm hC (X.mul_mem hτX hτX) (S.typeI_mul_of_typeII hτ2 hτ2)
  rw [← S.range_ι] at hττ
  obtain ⟨w, hw⟩ := hττ
  obtain ⟨s, hs2, ⟨x, hsx⟩, hs₁, hs₂⟩ := S.exists_involution hw.symm
  have hsX : s ∈ X := hsx ▸ X.mul_mem hτX (hA₁X (S.ι₁_mem x))
  have hsII : S.TypeII s := S.typeII_of_swap hp hW (hnorm _ hsX) hs₁
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hsN : s ∉ S.A₁ ⊔ S.A₂ := by
    intro hmem
    rw [← S.range_ι] at hmem
    obtain ⟨u, hu⟩ := hmem
    have h1 : s * S.a₁ * s⁻¹ ∈ S.A₁ := by
      rw [← hu, ι_apply]
      have hc : S.ι₂ u.2 * S.a₁ = S.a₁ * S.ι₂ u.2 := (S.comm _ S.a₁_mem _ (S.ι₂_mem u.2)).symm
      have : S.ι₁ u.1 * S.ι₂ u.2 * S.a₁ * (S.ι₁ u.1 * S.ι₂ u.2)⁻¹ =
          S.ι₁ u.1 * S.a₁ * (S.ι₁ u.1)⁻¹ := by
        calc S.ι₁ u.1 * S.ι₂ u.2 * S.a₁ * (S.ι₁ u.1 * S.ι₂ u.2)⁻¹
            = S.ι₁ u.1 * (S.ι₂ u.2 * S.a₁ * (S.ι₂ u.2)⁻¹) * (S.ι₁ u.1)⁻¹ := by group
          _ = S.ι₁ u.1 * S.a₁ * (S.ι₁ u.1)⁻¹ := by rw [hc]; group
      rw [this]
      exact S.A₁.mul_mem (S.A₁.mul_mem (S.ι₁_mem _) S.a₁_mem) (S.A₁.inv_mem (S.ι₁_mem _))
    have h2 := hs₁ S.a₁ S.a₁_mem
    have h3 : s * S.a₁ * s⁻¹ ∈ S.A₁ ⊓ S.A₂ := ⟨h1, h2⟩
    rw [S.inf, Subgroup.mem_bot] at h3
    apply S.a₁_ne_one hp
    calc S.a₁ = s⁻¹ * (s * S.a₁ * s⁻¹) * s := by group
      _ = 1 := by rw [h3]; group
  have hcosets : ∀ m ∈ X, m ∈ S.A₁ ⊔ S.A₂ ∨ m * s⁻¹ ∈ S.A₁ ⊔ S.A₂ := by
    intro m hm
    rcases S.typeI_or_typeII hp hW (hnorm m hm) with hI | hII
    · exact Or.inl (S.mem_sup_of_typeI hW hA₁X hA₂X hnorm hC hm hI)
    · exact Or.inr (S.mem_sup_of_typeI hW hA₁X hA₂X hnorm hC (X.mul_mem hm (X.inv_mem hsX))
        (by rw [hsinv]; exact S.typeI_mul_of_typeII hII hsII))
  have hfact : ∀ n ∈ S.A₁ ⊔ S.A₂, ∃ a ∈ S.A₁, ∃ b ∈ S.A₂, n = a * b := by
    intro n hn
    rw [← S.range_ι] at hn
    obtain ⟨u, rfl⟩ := hn
    exact ⟨S.ι₁ u.1, S.ι₁_mem _, S.ι₂ u.2, S.ι₂_mem _, S.ι_apply u⟩
  exact S14110.nonempty_mulEquiv_wreath X (S.A₁ ⊔ S.A₂) S.A₁ S.A₂ s (sup_le hA₁X hA₂X) hsX
    le_sup_left le_sup_right S.comm (fun x hx1 hx2 => by
      have : x ∈ S.A₁ ⊓ S.A₂ := ⟨hx1, hx2⟩
      rwa [S.inf, Subgroup.mem_bot] at this) hs2 hsN hcosets hfact hs₁ hs₂
    (S.e₁.trans dihEquivPerm3151b)

omit [Finite W] in
theorem eq_one_of_pow_mem_sup (S : SixData151b W 3) {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q)
    {y : MulAut W} (hy : y ∈ S.A₁ ⊔ S.A₂) {j : ℕ} (hyq : y ^ (q ^ j) = 1) : y = 1 := by
  rw [← S.range_ι] at hy
  obtain ⟨w, rfl⟩ := hy
  have hw : w ^ (q ^ j) = 1 := S.ι_injective (by rw [map_pow, hyq, map_one])
  have h36 : w ^ 36 = 1 := by
    have : ∀ w : DihedralGroup 3 × DihedralGroup 3, w ^ 36 = 1 := by decide
    exact this w
  have hdvd1 : orderOf w ∣ q ^ j := orderOf_dvd_of_pow_eq_one hw
  have hdvd2 : orderOf w ∣ 36 := orderOf_dvd_of_pow_eq_one h36
  have hcop : Nat.Coprime (q ^ j) 36 := by
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd hq]
    intro h
    have h36 : q ≤ 36 := Nat.le_of_dvd (by norm_num) h
    interval_cases q <;> first | omega | exact absurd hq (by norm_num)
  have : orderOf w = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
  rw [orderOf_eq_one_iff.mp this, map_one]

theorem centralizer_eq_one3 (S : SixData151b W 3) (hW : ∀ w : W, w ^ 2 = 1)
    (hcard : Nat.card W = 256) {X : Subgroup (MulAut W)} (hA₁X : S.A₁ ≤ X) (hA₂X : S.A₂ ≤ X)
    (hnorm : ∀ g ∈ X, ∀ z ∈ S.A₁ ⊔ S.A₂, g * z * g⁻¹ ∈ S.A₁ ⊔ S.A₂)
    (hsolv : Group.IsSolvable ↥X) (hO2 : ∀ N : Subgroup ↥X, N.Normal → IsPGroup 2 N → N = ⊥)
    {M : Type} [Group M] [Finite M] (φ : M →* ↥X) (hφ : Function.Surjective φ)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup M) ≤ 2) :
    ∀ c ∈ X, (∀ z ∈ S.A₁ ⊔ S.A₂, c * z = z * c) → c = 1 := by
  have hp : (3 : ℕ) = 3 ∨ (3 : ℕ) = 5 := Or.inl rfl
  have hA₀X : S.A₁ ⊔ S.A₂ ≤ X := sup_le hA₁X hA₂X
  have hR : ∀ q : ℕ, q.Prime → 5 ≤ q → ∀ N : Subgroup ↥X, N.Normal → IsPGroup q N → N = ⊥ := by
    intro q hq hq5 N hN hNp
    by_contra hne
    have : Fact q.Prime := ⟨hq⟩
    have hdvd : q ∣ Nat.card N := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hNp
      have hn0 : n ≠ 0 := by
        rintro rfl
        exact hne (Subgroup.card_eq_one.mp (by simpa using hn))
      rw [hn]
      exact dvd_pow_self q hn0
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' q hdvd
    have hcq : ((c : ↥X) : MulAut W) ^ q = 1 := by
      have h1 : c ^ q = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
      have := congrArg (fun y : N => ((y : ↥X) : MulAut W)) h1
      simpa using this
    have hcomm : ∀ z ∈ S.A₁ ⊔ S.A₂,
        ((c : ↥X) : MulAut W) * z = z * ((c : ↥X) : MulAut W) := by
      intro z hz
      have hk : (c : ↥X) * ⟨z, hA₀X hz⟩ * (c : ↥X)⁻¹ * ⟨z, hA₀X hz⟩⁻¹ ∈ N := by
        have h1 := hN.conj_mem (c : ↥X)⁻¹ (N.inv_mem c.2) ⟨z, hA₀X hz⟩
        have h2 := N.mul_mem c.2 h1
        have e : (c : ↥X) * ⟨z, hA₀X hz⟩ * (c : ↥X)⁻¹ * ⟨z, hA₀X hz⟩⁻¹ =
            (c : ↥X) * (⟨z, hA₀X hz⟩ * (c : ↥X)⁻¹ * ⟨z, hA₀X hz⟩⁻¹) := by group
        rw [e]
        exact h2
      have hkA : ((c : ↥X) : MulAut W) * z * ((c : ↥X) : MulAut W)⁻¹ * z⁻¹ ∈ S.A₁ ⊔ S.A₂ :=
        (S.A₁ ⊔ S.A₂).mul_mem (hnorm _ (c : ↥X).2 z hz) ((S.A₁ ⊔ S.A₂).inv_mem hz)
      obtain ⟨j, hj⟩ := hNp ⟨_, hk⟩
      have hj' : (((c : ↥X) : MulAut W) * z * ((c : ↥X) : MulAut W)⁻¹ * z⁻¹) ^ (q ^ j) = 1 := by
        have := congrArg (fun y : N => ((y : ↥X) : MulAut W)) hj
        simpa using this
      have h0 := S.eq_one_of_pow_mem_sup hq hq5 hkA hj'
      exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h0)).symm ▸ rfl
    have h1c : ((c : ↥X) : MulAut W) = 1 :=
      S.eq_one_of_prime_ge_five hp hW hcard hq5 hcq (fun x hx => hcomm x (Subgroup.mem_sup_left hx))
        (fun x hx => hcomm x (Subgroup.mem_sup_right hx))
    have hc1 : c = 1 := Subtype.ext (Subtype.ext h1c)
    rw [hc1, orderOf_one] at hc
    omega
  have hA := a131Concl_of_solvable151b hsolv hO2 hR φ hφ hrk
  let a : ↥X := ⟨S.a₂, hA₂X S.a₂_mem⟩
  let s : ↥X := ⟨S.s₁, hA₁X S.s₁_mem⟩
  have ha3 : a ^ 3 = 1 := Subtype.ext (S.a₂_pow hp)
  have ha1 : a ≠ 1 := fun h => S.a₂_ne_one hp (congrArg Subtype.val h)
  have hs2 : s ^ 2 = 1 := Subtype.ext (S.s₁_sq hp)
  have hs1 : s ≠ 1 := fun h => S.s₁_ne_one hp (congrArg Subtype.val h)
  have has : s * a = a * s := Subtype.ext (S.comm _ S.s₁_mem _ S.a₂_mem)
  let rot : Subgroup (DihedralGroup 3 × DihedralGroup 3) :=
    { carrier := {w | ∃ i j : ZMod 3, w = (DihedralGroup.r i, DihedralGroup.r j)}
      one_mem' := ⟨0, 0, Prod.ext (DihedralGroup.r_zero).symm (DihedralGroup.r_zero).symm⟩
      mul_mem' := by
        rintro _ _ ⟨i, j, rfl⟩ ⟨i', j', rfl⟩
        exact ⟨i + i', j + j', Prod.ext (DihedralGroup.r_mul_r i i') (DihedralGroup.r_mul_r j j')⟩
      inv_mem' := by
        rintro _ ⟨i, j, rfl⟩
        exact ⟨-i, -j, Prod.ext (DihedralGroup.inv_r i) (DihedralGroup.inv_r j)⟩ }
  let P₃ : Subgroup (MulAut W) := rot.map S.ι
  have hP₃inv : ∀ g ∈ X, ∀ n ∈ P₃, g * n * g⁻¹ ∈ P₃ := by
    intro g hg n hn
    obtain ⟨w, ⟨i, j, rfl⟩, rfl⟩ := hn
    have hn' : S.ι (DihedralGroup.r i, DihedralGroup.r j) = S.a₁ ^ i.val * S.a₂ ^ j.val := by
      rw [S.ι_apply]
      exact congrArg₂ (· * ·) (S.ι₁_r hp i) (S.ι₂_r hp j)
    rw [hn']
    have hconj : g * (S.a₁ ^ i.val * S.a₂ ^ j.val) * g⁻¹ =
        (g * S.a₁ * g⁻¹) ^ i.val * (g * S.a₂ * g⁻¹) ^ j.val := by
      rw [conj_pow, conj_pow]; group
    rw [hconj]
    have hP : g * S.a₁ * g⁻¹ ∈ P₃ ∧ g * S.a₂ * g⁻¹ ∈ P₃ := by
      have m1 : ∀ k : ZMod 3, S.ι₁ (DihedralGroup.r k) ∈ P₃ := fun k =>
        ⟨(DihedralGroup.r k, 1), ⟨k, 0, by simp [DihedralGroup.r_zero]⟩, S.ι_inl _⟩
      have m2 : ∀ k : ZMod 3, S.ι₂ (DihedralGroup.r k) ∈ P₃ := fun k =>
        ⟨(1, DihedralGroup.r k), ⟨0, k, by simp [DihedralGroup.r_zero]⟩, S.ι_inr _⟩
      rcases S.typeI_or_typeII_exp hp hW (hnorm g hg) with
        ⟨k, k', -, -, h1, h2⟩ | ⟨k, k', -, -, h1, h2⟩
      · exact ⟨h1 ▸ m1 k, h2 ▸ m2 k'⟩
      · exact ⟨h1 ▸ m2 k, h2 ▸ m1 k'⟩
    exact P₃.mul_mem (P₃.pow_mem hP.1 _) (P₃.pow_mem hP.2 _)
  have hPn : (P₃.subgroupOf X).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hP₃inv g.1 g.2 n.1 hn⟩
  have hrot3 : ∀ i j : ZMod 3,
      ((DihedralGroup.r i, DihedralGroup.r j) : DihedralGroup 3 × DihedralGroup 3) ^ 3 = 1 := by
    decide
  have hP3 : IsPGroup 3 (P₃.subgroupOf X) := by
    intro x
    refine ⟨1, ?_⟩
    obtain ⟨w, ⟨i, j, rfl⟩, hw⟩ := Subgroup.mem_subgroupOf.mp x.2
    apply Subtype.ext
    apply Subtype.ext
    show ((x : ↥X) : MulAut W) ^ (3 ^ 1) = 1
    rw [← hw, ← map_pow, pow_one, hrot3 i j, map_one]
  have haP : a ∈ P₃.subgroupOf X :=
    Subgroup.mem_subgroupOf.mpr ⟨(1, DihedralGroup.r 1), ⟨0, 1, by simp [DihedralGroup.r_zero]⟩, rfl⟩
  let C : Subgroup ↥X :=
    { carrier := {c | ∀ z ∈ S.A₁ ⊔ S.A₂, (c : MulAut W) * z = z * (c : MulAut W)}
      one_mem' := fun z _ => by simp
      mul_mem' := fun {u v} hu hv z hz => (Commute.mul_left (hu z hz) (hv z hz)).eq
      inv_mem' := fun {u} hu z hz => (Commute.inv_left (hu z hz)).eq }
  have hCn : C.Normal :=
    ⟨fun n hn g z hz => by
      have hz' : (g : MulAut W)⁻¹ * z * (g : MulAut W) ∈ S.A₁ ⊔ S.A₂ := by
        have := hnorm _ (X.inv_mem g.2) z hz
        simpa using this
      have h1 := hn _ hz'
      show (g : MulAut W) * (n : MulAut W) * (g : MulAut W)⁻¹ * z =
        z * ((g : MulAut W) * (n : MulAut W) * (g : MulAut W)⁻¹)
      calc (g : MulAut W) * (n : MulAut W) * (g : MulAut W)⁻¹ * z
          = (g : MulAut W) * ((n : MulAut W) * ((g : MulAut W)⁻¹ * z * (g : MulAut W))) *
              (g : MulAut W)⁻¹ := by group
        _ = (g : MulAut W) * (((g : MulAut W)⁻¹ * z * (g : MulAut W)) * (n : MulAut W)) *
              (g : MulAut W)⁻¹ := by rw [h1]
        _ = z * ((g : MulAut W) * (n : MulAut W) * (g : MulAut W)⁻¹) := by group⟩
  have hCs : ∀ k ∈ C, k * s = s * k := fun k hk =>
    Subtype.ext (hk S.s₁ (Subgroup.mem_sup_left S.s₁_mem))
  have hCa : ∀ k ∈ C, k ∈ Subgroup.zpowers a → k = 1 := by
    intro k hk hka
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hka
    have hc := hk S.s₂ (Subgroup.mem_sup_right S.s₂_mem)
    have hcoe : (((a ^ m : ↥X)) : MulAut W) = S.a₂ ^ m := by simp [a]
    rw [hcoe] at hc
    have h2 : S.s₂ * S.a₂ ^ m * S.s₂⁻¹ = (S.a₂⁻¹) ^ m := by
      rw [← conj_zpow, S.s₂_a₂ hp]
    have h3 : S.s₂ * S.a₂ ^ m * S.s₂⁻¹ = S.a₂ ^ m := by
      calc S.s₂ * S.a₂ ^ m * S.s₂⁻¹ = (S.a₂ ^ m * S.s₂) * S.s₂⁻¹ := by rw [hc]
        _ = S.a₂ ^ m := by group
    have h4 : (S.a₂ ^ m) ^ 2 = 1 := by
      rw [pow_two]
      have : (S.a₂ ^ m)⁻¹ = S.a₂ ^ m := by rw [← inv_zpow, ← h2, h3]
      exact mul_eq_one_iff_eq_inv.mpr this.symm
    have h5 : (S.a₂ ^ m) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
      simp [show S.a₂ ^ (3 : ℤ) = 1 from by exact_mod_cast S.a₂_pow hp]
    have h6 : S.a₂ ^ m = 1 := by
      have : S.a₂ ^ m = (S.a₂ ^ m) ^ 3 * ((S.a₂ ^ m) ^ 2)⁻¹ := by group
      rw [this, h5, h4]; simp
    exact Subtype.ext (by simpa [a] using h6)
  have hbot := eq_bot_of_centralizer151b hsolv hO2 hR hA ha3 ha1 hs2 hs1 has hPn hP3 haP
    (C := C) hCs hCa
  intro c hcX hc
  have hmem : (⟨c, hcX⟩ : ↥X) ∈ C := hc
  rw [hbot, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

theorem nonempty_mulEquiv_wreath3_of_solvable (S : SixData151b W 3) (hW : ∀ w : W, w ^ 2 = 1)
    (hcard : Nat.card W = 256) {X : Subgroup (MulAut W)} (hA₁X : S.A₁ ≤ X) (hA₂X : S.A₂ ≤ X)
    (hτX : S.τ ∈ X) (hnorm : ∀ g ∈ X, ∀ z ∈ S.A₁ ⊔ S.A₂, g * z * g⁻¹ ∈ S.A₁ ⊔ S.A₂)
    (hsolv : Group.IsSolvable ↥X) (hO2 : ∀ N : Subgroup ↥X, N.Normal → IsPGroup 2 N → N = ⊥)
    {M : Type} [Group M] [Finite M] (φ : M →* ↥X) (hφ : Function.Surjective φ)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup M) ≤ 2) :
    Nonempty (↥X ≃* Equiv.Perm (Fin 3) ≀ᵣ Multiplicative (ZMod 2)) :=
  S.nonempty_mulEquiv_wreath3 hW hA₁X hA₂X hτX hnorm
    (S.centralizer_eq_one3 hW hcard hA₁X hA₂X hnorm hsolv hO2 φ hφ hrk)

end Assembly

end SixData151b

end CFSG.Quasithin
