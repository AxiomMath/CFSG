module

public import CFSG.RankThree.PartTwo.Sec10.Item102Proof
public import CFSG.RankThree.PartTwo.KFacts.KS10Lines
public import CFSG.RankThree.PartTwo.Sec11.Item116Coords

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open scoped Matrix

section General

variable {G : Type*} [Group G]

theorem map_conj_zpowers (g c : G) :
    (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers (g * c * g⁻¹) := by
  rw [MonoidHom.map_zpowers]
  rfl

theorem map_conj_normalizer_zpowers (g c : G) :
    (Subgroup.normalizer (Subgroup.zpowers c : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.normalizer (Subgroup.zpowers (g * c * g⁻¹) : Set G) := by
  rw [← map_conj_zpowers, Subgroup.map_equiv_normalizer_eq]

theorem IsSylowOf.map_conj [Finite G] {p : ℕ} [Fact p.Prime] {P K : Subgroup G}
    (h : IsSylowOf p P K) (g : G) :
    IsSylowOf p (P.map (MulAut.conj g).toMonoidHom) (K.map (MulAut.conj g).toMonoidHom) :=
  CFSG.ABGLocalTools.isSylowOf_of_card (Subgroup.map_mono h.le) (by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Subgroup.card_map_of_injective (MulAut.conj g).injective, h.card_eq])

theorem mem_map_conj_iff {P : Subgroup G} {g x : G} :
    x ∈ P.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ P := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    change g⁻¹ * (g * y * g⁻¹) * g ∈ P
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by change g * (g⁻¹ * x * g) * g⁻¹ = x; group⟩

end General

section Coords

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] {A : Subgroup G}

theorem conj_coord_eq (f : Multiplicative (Fin 3 → ZMod 3) ≃* A)
    (w : Subgroup.normalizer (A : Set G)) (v : Fin 3 → ZMod 3) :
    (w : G) * (f (Multiplicative.ofAdd v) : G) * (w : G)⁻¹ =
      (f (Multiplicative.ofAdd (Sec11.coordMat f w *ᵥ v)) : G) := by
  rw [← Sec12.wAction_apply f w v, Sec11.coordMat, LinearMap.toMatrix'_mulVec]
  rfl

theorem false_of_lines {A : Subgroup G} [Finite A] {c b e d x y : G}
    (hexp : ∀ u ∈ A, u ^ 3 = 1) (hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u)
    (h27 : Nat.card A = 27) (hcA : c ∈ A) (hbA : b ∈ A) (heA : e ∈ A) (hdA : d ∈ A)
    (hgen : Subgroup.closure {c, b, e} = A) (hdc : d ∉ Subgroup.zpowers c)
    (hbcd : b ∉ Subgroup.closure ({c, d} : Set G))
    (hxN : x ∈ Subgroup.normalizer (A : Set G)) (hyN : y ∈ Subgroup.normalizer (A : Set G))
    (hxc : x * c * x⁻¹ = c) (hxd : x * d * x⁻¹ = d)
    (hxA : ∀ u ∈ A, x * u * x⁻¹ * u⁻¹ ∈ Subgroup.zpowers d) (hx1 : ∃ u ∈ A, x * u * x⁻¹ ≠ u)
    (hyb : y * b * y⁻¹ = b) (hye : y * e * y⁻¹ = e)
    (hyc : y * c * y⁻¹ * c⁻¹ ∈ Subgroup.zpowers e) (hyc1 : y * c * y⁻¹ ≠ c)
    (hb : ∃ g₀ : G, b = g₀ * c * g₀⁻¹)
    (hW1 : ∀ g : G, g * c * g⁻¹ ∈ Subgroup.closure ({c, d} : Set G) →
      g * c * g⁻¹ ∈ Subgroup.zpowers c)
    (hW2 : ∀ g : G, g * c * g⁻¹ ∈ Subgroup.closure ({b, e} : Set G) →
      g * c * g⁻¹ ∈ Subgroup.zpowers b) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g₀, rfl⟩ := hb
  obtain ⟨f, hfc, hfb, hfe, hfv⟩ := Sec11.exists_coords_triple hcomm hexp h27 hcA hbA heA hgen
  have hfc' : (f (Multiplicative.ofAdd (Pi.single 0 1)) : G) = c := congrArg Subtype.val hfc
  have hfb' : (f (Multiplicative.ofAdd (Pi.single 1 1)) : G) = g₀ * c * g₀⁻¹ :=
    congrArg Subtype.val hfb
  have hfe' : (f (Multiplicative.ofAdd (Pi.single 2 1)) : G) = e := congrArg Subtype.val hfe
  set δ : Fin 3 → ZMod 3 := Multiplicative.toAdd (f.symm ⟨d, hdA⟩) with hδdef
  have hfδ : (f (Multiplicative.ofAdd δ) : G) = d := by simp [hδdef]
  have hfadd : ∀ u v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd (u + v)) : G) =
      (f (Multiplicative.ofAdd u) : G) * (f (Multiplicative.ofAdd v) : G) := by
    intro u v
    rw [ofAdd_add, map_mul, Subgroup.coe_mul]
  have hfsmul : ∀ (r : ZMod 3) (v : Fin 3 → ZMod 3), (f (Multiplicative.ofAdd (r • v)) : G) =
      (f (Multiplicative.ofAdd v) : G) ^ r.val := by
    intro r v
    have : r • v = r.val • v := by
      ext i
      simp [ZMod.natCast_val]
    rw [this, ofAdd_nsmul, map_pow, Subgroup.coe_pow]
  have hfinj : ∀ u v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd u) : G) =
      (f (Multiplicative.ofAdd v) : G) → u = v := fun u v h =>
    Multiplicative.ofAdd.injective (f.injective (Subtype.ext h))
  have hzpow : ∀ (s : Fin 3) (k : ℤ), (f (Multiplicative.ofAdd (Pi.single s 1)) : G) ^ k =
      (f (Multiplicative.ofAdd ((k : ZMod 3) • Pi.single s 1)) : G) := by
    intro s k
    rw [hfsmul, ← Sec11.zpow_eq_pow_val (hexp _ (f _).2)]
  have hd3 := hexp d hdA
  have he3 := hexp e heA
  obtain ⟨m₁, hm₁⟩ := Subgroup.mem_zpowers_iff.mp (hxA _ hbA)
  obtain ⟨m₂, hm₂⟩ := Subgroup.mem_zpowers_iff.mp (hxA e heA)
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hyc
  set r : ZMod 3 := (m₁ : ZMod 3) with hr
  set q : ZMod 3 := (m₂ : ZMod 3) with hq
  set t : ZMod 3 := (n : ZMod 3) with ht
  have hxb : x * (g₀ * c * g₀⁻¹) * x⁻¹ = (g₀ * c * g₀⁻¹) * d ^ r.val := by
    have h1 : x * (g₀ * c * g₀⁻¹) * x⁻¹ = d ^ m₁ * (g₀ * c * g₀⁻¹) := by rw [hm₁]; group
    rw [h1, Sec11.zpow_eq_pow_val hd3, hcomm _ (A.pow_mem hdA _) _ hbA]
  have hxe : x * e * x⁻¹ = e * d ^ q.val := by
    have h1 : x * e * x⁻¹ = d ^ m₂ * e := by rw [hm₂]; group
    rw [h1, Sec11.zpow_eq_pow_val hd3, hcomm _ (A.pow_mem hdA _) _ heA]
  have hycc : y * c * y⁻¹ = c * e ^ t.val := by
    have h1 : y * c * y⁻¹ = e ^ n * c := by rw [hn]; group
    rw [h1, Sec11.zpow_eq_pow_val he3, hcomm _ (A.pow_mem heA _) _ hcA]
  set X : Subgroup.normalizer (A : Set G) := ⟨x, hxN⟩ with hX
  set Y : Subgroup.normalizer (A : Set G) := ⟨y, hyN⟩ with hY
  have hMX : Sec11.coordMat f X = KFacts.lineMatX r q δ := by
    apply Sec11.coordMat_eq'
    · have hcol : (fun i => KFacts.lineMatX r q δ i 0) = Pi.single 0 1 := by
        ext i; fin_cases i <;> simp [KFacts.lineMatX]
      rw [hcol, hfc']
      exact hxc
    · have hcol : (fun i => KFacts.lineMatX r q δ i 1) = Pi.single 1 1 + r • δ := by
        ext i; fin_cases i <;> simp [KFacts.lineMatX]
      rw [hcol, hfadd, hfsmul, hfb', hfδ]
      exact hxb
    · have hcol : (fun i => KFacts.lineMatX r q δ i 2) = Pi.single 2 1 + q • δ := by
        ext i; fin_cases i <;> simp [KFacts.lineMatX]
      rw [hcol, hfadd, hfsmul, hfe', hfδ]
      exact hxe
  have hMY : Sec11.coordMat f Y = KFacts.lineMatY t := by
    apply Sec11.coordMat_eq'
    · have hcol : (fun i => KFacts.lineMatY t i 0) = Pi.single 0 1 + t • Pi.single 2 1 := by
        ext i; fin_cases i <;> simp [KFacts.lineMatY]
      rw [hcol, hfadd, hfsmul, hfc', hfe']
      exact hycc
    · have hcol : (fun i => KFacts.lineMatY t i 1) = Pi.single 1 1 := by
        ext i; fin_cases i <;> simp [KFacts.lineMatY]
      rw [hcol, hfb']
      exact hyb
    · have hcol : (fun i => KFacts.lineMatY t i 2) = Pi.single 2 1 := by
        ext i; fin_cases i <;> simp [KFacts.lineMatY]
      rw [hcol, hfe']
      exact hye
  have hval0 : ∀ u : ZMod 3, u.val = 0 → u = 0 := fun u hu => (ZMod.val_eq_zero u).mp hu
  have ht0 : t ≠ 0 := by
    intro h0
    apply hyc1
    rw [hycc, h0, ZMod.val_zero, pow_zero, mul_one]
  have hcen : ∀ g : G, g * c * g⁻¹ = c → g * (g₀ * c * g₀⁻¹) * g⁻¹ = g₀ * c * g₀⁻¹ →
      g * e * g⁻¹ = e → ∀ u ∈ A, g * u * g⁻¹ = u := by
    intro g h1 h2 h3 u hu
    have hle : Subgroup.closure ({c, g₀ * c * g₀⁻¹, e} : Set G) ≤
        Subgroup.centralizer ({g} : Set G) := by
      rw [Subgroup.closure_le]
      intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rcases hv with hv | hv | hv <;> rw [hv]
      · exact Sec11.mul_comm_of_conj_eq h1
      · exact Sec11.mul_comm_of_conj_eq h2
      · exact Sec11.mul_comm_of_conj_eq h3
    have := Subgroup.mem_centralizer_singleton_iff.mp (hle (hgen ▸ hu))
    rw [← this, mul_inv_cancel_right]
  have hrq : r ≠ 0 ∨ q ≠ 0 := by
    by_contra hrq
    push Not at hrq
    obtain ⟨u, hu, hu1⟩ := hx1
    apply hu1
    refine hcen x hxc ?_ ?_ u hu
    · rw [hxb, hrq.1, ZMod.val_zero, pow_zero, mul_one]
    · rw [hxe, hrq.2, ZMod.val_zero, pow_zero, mul_one]
  have hfδv : d = c ^ (δ 0).val * (g₀ * c * g₀⁻¹) ^ (δ 1).val * e ^ (δ 2).val := by
    rw [← hfδ, hfv]
  have hδ1 : δ 1 ≠ 0 ∨ δ 2 ≠ 0 := by
    by_contra hδ
    push Not at hδ
    apply hdc
    rw [hfδv, hδ.1, hδ.2, ZMod.val_zero, pow_zero, pow_zero, mul_one, mul_one]
    exact Subgroup.npow_mem_zpowers c _
  have hδ2 : δ 2 ≠ 0 ∨ δ 1 = 0 := by
    by_contra hδ
    push Not at hδ
    apply hbcd
    have hd' : d = c ^ (δ 0).val * (g₀ * c * g₀⁻¹) ^ (δ 1).val := by
      rw [hfδv, hδ.1, ZMod.val_zero, pow_zero, mul_one]
    have hmem : (g₀ * c * g₀⁻¹) ^ (δ 1).val ∈ Subgroup.closure ({c, d} : Set G) := by
      have : (g₀ * c * g₀⁻¹) ^ (δ 1).val = (c ^ (δ 0).val)⁻¹ * d := by rw [hd']; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _
        (Subgroup.subset_closure (by simp)) _)) (Subgroup.subset_closure (by simp))
    have hv12 : (δ 1).val = 1 ∨ (δ 1).val = 2 := by
      have h1 : (δ 1).val < 3 := ZMod.val_lt _
      have h2 : (δ 1).val ≠ 0 := fun h0 => hδ.2 (hval0 _ h0)
      omega
    have hb3 := hexp _ hbA
    rcases hv12 with h1 | h1
    · rw [h1, pow_one] at hmem
      exact hmem
    · rw [h1] at hmem
      have : g₀ * c * g₀⁻¹ = ((g₀ * c * g₀⁻¹) ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hb3, one_mul, pow_one]
      rw [this]
      exact Subgroup.pow_mem _ hmem 2
  have hXδ : KFacts.lineMatX r q δ *ᵥ δ = δ := by
    rw [← hMX]
    apply hfinj
    rw [← conj_coord_eq, hfδ]
    exact hxd
  have key2 : ∀ (w : Subgroup.normalizer (A : Set G)) (sv : Fin 3) (g : G),
      (f (Multiplicative.ofAdd (Pi.single sv 1)) : G) = g * c * g⁻¹ →
      KFacts.LineBadTwo (Sec11.coordMat f w *ᵥ Pi.single sv 1) → False := by
    intro w sv g hg ⟨hv0, hv2⟩
    set v := Sec11.coordMat f w *ᵥ Pi.single sv 1 with hv
    have hconj : (f (Multiplicative.ofAdd v) : G) = ((w : G) * g) * c * ((w : G) * g)⁻¹ := by
      rw [hv, ← conj_coord_eq, hg]
      group
    have hmem : ((w : G) * g) * c * ((w : G) * g)⁻¹ ∈
        Subgroup.closure ({g₀ * c * g₀⁻¹, e} : Set G) := by
      rw [← hconj, hfv, hv0, ZMod.val_zero, pow_zero, one_mul]
      exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
        (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
    have h1 := hW2 _ hmem
    rw [← hconj, ← hfb'] at h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    rw [hzpow] at hk
    have h2 := hfinj _ _ hk
    apply hv2
    rw [← h2]
    simp
  have key1 : ∀ (w : Subgroup.normalizer (A : Set G)) (sv : Fin 3) (g : G),
      (f (Multiplicative.ofAdd (Pi.single sv 1)) : G) = g * c * g⁻¹ →
      KFacts.LineBadOne δ (Sec11.coordMat f w *ᵥ Pi.single sv 1) → False := by
    intro w sv g hg ⟨l, m, hm, hvlm⟩
    set v := Sec11.coordMat f w *ᵥ Pi.single sv 1 with hv
    have hconj : (f (Multiplicative.ofAdd v) : G) = ((w : G) * g) * c * ((w : G) * g)⁻¹ := by
      rw [hv, ← conj_coord_eq, hg]
      group
    have hmem : ((w : G) * g) * c * ((w : G) * g)⁻¹ ∈ Subgroup.closure ({c, d} : Set G) := by
      rw [← hconj, hvlm, hfadd, hfsmul, hfsmul, hfc', hfδ]
      exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
        (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
    have h1 := hW1 _ hmem
    rw [← hconj, ← hfc'] at h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    rw [hzpow] at hk
    have h2 := hfinj _ _ hk
    rw [hvlm] at h2
    have hδ0 : ∀ i : Fin 3, i ≠ 0 → δ i = 0 := by
      intro i hi
      have h3 := congrFun h2 i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, hi, ite_false,
        mul_zero, zero_add] at h3
      rcases mul_eq_zero.mp h3.symm with h4 | h4
      · exact absurd h4 hm
      · exact h4
    rcases hδ1 with h5 | h5
    · exact h5 (hδ0 1 (by decide))
    · exact h5 (hδ0 2 (by decide))
  have hc1 : (f (Multiplicative.ofAdd (Pi.single 0 1)) : G) = 1 * c * 1⁻¹ := by
    rw [hfc']; group
  rcases KFacts.lines_cases t r q δ ht0 hrq hδ1 hδ2 hXδ with h | h | h | h | h | h
  · exact key2 X 1 g₀ hfb' (by rwa [hMX])
  · exact key1 Y 0 1 hc1 (by rwa [hMY])
  · exact key2 (X * Y) 0 1 hc1 (by rwa [Sec11.coordMat_mul, hMX, hMY])
  · exact key2 (X * (Y * Y)) 0 1 hc1 (by rwa [Sec11.coordMat_mul, Sec11.coordMat_mul, hMX, hMY])
  · exact key2 (X * X * Y) 0 1 hc1 (by rwa [Sec11.coordMat_mul, Sec11.coordMat_mul, hMX, hMY])
  · exact key2 (X * X * (Y * Y)) 0 1 hc1
      (by rwa [Sec11.coordMat_mul, Sec11.coordMat_mul, Sec11.coordMat_mul, hMX, hMY])

end Coords

section Std

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R : Subgroup G}

theorem Sec10Std.d_commute_of_mem_R (h45 : Sec4.Item4_5) (h : Sec10Std G A c L a R) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) {r : G} (hr : r ∈ R) : r * d = d * r := by
  have hdRL := h.d_mem_inf hdL
  have hdA := h.d_mem_A hdL
  obtain ⟨t, htT, z, hzZ, rfl⟩ := h.exists_mul_of_mem_R h45 hr
  obtain ⟨i, y, hy, rfl⟩ := exists_zpow_mul_of_mem_sup_zpowers'
    (Subgroup.zpowers_le.mpr h.a_mem_normalizer_inf) htT
  have hda : Commute d (a ^ i) := (show Commute d a from h.comm hdA h.a_mem).zpow_right i
  have hdy : Commute d y :=
    congrArg Subtype.val (h.isElemAbelian_inf.1.is_comm.comm ⟨d, hdRL⟩ ⟨y, hy⟩)
  have hdz : Commute d z := h.commute_of_mem_thetaQuotCentralizer hzZ.1 hzZ.2 hdRL
  exact ((hda.mul_right hdy).mul_right hdz).symm.eq

omit [Finite G] in
theorem conj_mem_of_commute_conj (hF : A ∈ partTwoF G) {g u : G} (hu3 : u ^ 3 = 1)
    (hcu : ∀ v ∈ A, (g * v * g⁻¹) * u = u * (g * v * g⁻¹)) : g⁻¹ * u * g ∈ A := by
  have h3 : (g⁻¹ * u * g) ^ 3 = 1 := by
    have := conj_pow (a := g⁻¹) (b := u) (i := 3)
    rw [inv_inv] at this
    rw [this, hu3]
    group
  apply Sec15.mem_of_mem_partTwoF hF h3
  intro v hv
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := hcu v hv
  calc v * (g⁻¹ * u * g) = g⁻¹ * ((g * v * g⁻¹) * u) * g := by group
    _ = g⁻¹ * (u * (g * v * g⁻¹)) * g := by rw [h1]
    _ = g⁻¹ * u * g * v := by group

omit [Finite G] in
theorem zpowers_eq_of_mem_of_ne_one {x y : G} (hx : orderOf x = 3) (hy : y ∈ Subgroup.zpowers x)
    (hy1 : y ≠ 1) : Subgroup.zpowers y = Subgroup.zpowers x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact le_antisymm (Subgroup.zpowers_le.mpr hy)
    (Subgroup.zpowers_le.mpr (KFacts.mem_zpowers_of_mem_zpowers_of_ne_one' hx hy hy1))

end Std

theorem rank3II_10_4 (h45 : Sec4.Item4_5) (h97 : Sec9.Item97) (h98 : Sec9.Item98) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
      (R : Subgroup G), Sec10Std G A c L a R →
        ∃ g : G, (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom ≤ sec10D c R L ∧
          (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom ≠ Subgroup.zpowers c := by
  intro G _ _ A c L a R h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcon
  push Not at hcon
  set D := sec10D c R L with hDdef
  have hW : ∀ g : G, g * c * g⁻¹ ∈ D → g * c * g⁻¹ ∈ Subgroup.zpowers c := by
    intro g hg
    have h1 := hcon g (by rw [map_conj_zpowers, Subgroup.zpowers_le]; exact hg)
    rw [map_conj_zpowers] at h1
    rw [← h1]
    exact Subgroup.mem_zpowers _
  obtain ⟨d, hdL, hdo, hA⟩ := exists_inf_eq_zpowers h97 h.toHyp91
  have hexp : ∀ u ∈ A, u ^ 3 = 1 := fun u hu => h.pow_three hu
  have hcommA : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv => h.comm hu hv
  have h27 := h.card_eq
  have hcA := h.mem_A
  have haA := h.a_mem
  have hc3 := hexp c hcA
  have ha3 := hexp a haA
  have hco := h.orderOf_c
  have hdRL := h.d_mem_inf hdL
  have hdA := h.d_mem_A hdL
  have hd3 := hexp d hdA
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hdo
    norm_num at hdo
  have hcD : c ∈ D := h.c_mem_D
  have hdD : d ∈ D := h.inf_le_D hdRL
  have hcdD : Subgroup.closure ({c, d} : Set G) ≤ D := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hcD
    · exact hdD
  have hdc : d ∉ Subgroup.zpowers c := by
    intro hdc
    apply h.c_not_mem_L
    exact Subgroup.zpowers_le.mpr hdRL.2 (KFacts.mem_zpowers_of_mem_zpowers_of_ne_one' hco hdc hd1)
  obtain ⟨g₀, hg₀A, hg₀ne⟩ := h98 G A c L a R h.toHyp91
  rw [map_conj_zpowers] at hg₀A hg₀ne
  set b := g₀ * c * g₀⁻¹ with hb
  have hbA : b ∈ A := hg₀A (Subgroup.mem_zpowers b)
  have hbo : orderOf b = 3 := by
    rw [hb, ← hco]
    exact orderOf_injective (MulAut.conj g₀).toMonoidHom (MulAut.conj g₀).injective c
  have hb1 : b ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hbo
    norm_num at hbo
  have hbD : b ∉ D := fun hbD => hg₀ne (zpowers_eq_of_mem_of_ne_one hco (hW g₀ hbD) hb1)
  have hbc : b ∉ Subgroup.zpowers c := fun hbc =>
    hg₀ne (zpowers_eq_of_mem_of_ne_one hco hbc hb1)
  have hbN : A ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) := fun u hu =>
    Sec10.mem_normalizer_zpowers_of_conj_mem (by
      rw [hcommA u hu b hbA, mul_inv_cancel_right]
      exact Subgroup.mem_zpowers b)
  have hR0 : IsSylowOf 3 (R.map (MulAut.conj g₀).toMonoidHom)
      (Subgroup.normalizer (Subgroup.zpowers b : Set G)) := by
    have h1 := IsSylowOf.map_conj h.isSylowOf g₀
    rwa [map_conj_normalizer_zpowers] at h1
  have hA3 : IsPGroup 3 A := fun u => ⟨1, Subtype.ext (by simpa using hexp u u.2)⟩
  obtain ⟨Q, hQ⟩ := (hA3.comap_subtype
    (K := Subgroup.normalizer (Subgroup.zpowers b : Set G))).exists_le_sylow
  set S := (Q : Subgroup (Subgroup.normalizer (Subgroup.zpowers b : Set G))).map
    (Subgroup.normalizer (Subgroup.zpowers b : Set G)).subtype with hS
  have hSsyl : IsSylowOf 3 S (Subgroup.normalizer (Subgroup.zpowers b : Set G)) := ⟨Q, rfl⟩
  have hAS : A ≤ S := fun u hu =>
    ⟨⟨u, hbN hu⟩, hQ (Subgroup.mem_subgroupOf.mpr hu), rfl⟩
  obtain ⟨h', hh'N, hh'⟩ := IsSylowOf.exists_mem_conj hR0 hSsyl
  set k := h' * g₀ with hk
  have hAk : ∀ u ∈ A, k⁻¹ * u * k ∈ R := by
    intro u hu
    have h1 := (hh' u).mp (hAS hu)
    rw [mem_map_conj_iff] at h1
    rw [hk]
    simpa [mul_assoc] using h1
  have hkc : Subgroup.zpowers (k * c * k⁻¹) = Subgroup.zpowers b := by
    have e1 : k * c * k⁻¹ = h' * b * h'⁻¹ := by rw [hk, hb]; group
    rw [e1, ← map_conj_zpowers]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hh'N
  set w := k⁻¹ * c * k with hw
  have hwR : w ∈ R := hAk c hcA
  have hwD : w ∉ D := by
    intro hwD
    have h1 : k⁻¹ * c * k⁻¹⁻¹ ∈ Subgroup.zpowers c := hW k⁻¹ (by rw [inv_inv]; exact hwD)
    rw [inv_inv] at h1
    have h2 : c ∈ Subgroup.zpowers (k * c * k⁻¹) := by
      rw [← map_conj_zpowers]
      exact ⟨k⁻¹ * c * k, h1, by change k * (k⁻¹ * c * k) * k⁻¹ = c; group⟩
    rw [hkc] at h2
    exact hg₀ne (zpowers_eq_of_mem_of_ne_one hbo h2 h.ne_one).symm
  have hΩ := (rank3II_10_2 h45 h97 G A c L a R h).1
  have hw3 : w ^ 3 = 1 := by
    rw [hw]
    have := conj_pow (a := k⁻¹) (b := c) (i := 3)
    rw [inv_inv] at this
    rw [this, hc3]
    group
  have hwΩ : w ∈ Subgroup.zpowers a ⊔ D := by
    rw [← hΩ]
    exact Subgroup.subset_closure ⟨hwR, hw3⟩
  have haND : a ∈ Subgroup.normalizer (D : Set G) := by
    apply Sec11.mem_normalizer_of_forall_conj_mem
    have hle : D ≤ D.comap (MulAut.conj a⁻¹).toMonoidHom := by
      rw [hDdef, sec10D]
      apply sup_le
      · rw [Subgroup.zpowers_le, Subgroup.mem_comap]
        change a⁻¹ * c * a⁻¹⁻¹ ∈ _
        rw [inv_inv, mul_assoc, ← h.comm haA hcA, inv_mul_cancel_left]
        exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
      · intro u hu
        rw [Subgroup.mem_comap]
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp
          (Subgroup.inv_mem _ h.a_mem_normalizer_inf) u).mp hu)
    intro u hu
    have := hle hu
    rw [Subgroup.mem_comap] at this
    simpa using this
  obtain ⟨j, z, hzD, hwz⟩ := exists_zpow_mul_of_mem_sup_zpowers' (Subgroup.zpowers_le.mpr haND)
    hwΩ
  have hzRL : ∀ u ∈ R ⊓ L, u * z = z * u := fun u hu =>
    congrArg Subtype.val (h.isElemAbelian_D.1.is_comm.comm ⟨u, h.inf_le_D hu⟩ ⟨z, hzD⟩)
  have hdZ := fun r (hr : r ∈ R) => h.d_commute_of_mem_R h45 hdL hr
  have heA : k * d * k⁻¹ ∈ A := by
    have h1 := conj_mem_of_commute_conj (A := A) h.mem_partTwoF (g := k⁻¹) (u := d) hd3
      (fun v hv => (hdZ _ (by simpa using hAk v hv)))
    simpa using h1
  set e := k * d * k⁻¹ with he
  have hCa := h.inf_centralizer_a hdL hA
  obtain ⟨x, hxRL, hδx, hδx1⟩ := KFacts.exists_commMap_mem_zpowers h.isElemAbelian_inf
    h.card_inf ha3 h.a_mem_normalizer_inf hdRL hd1 (by rw [h.comm haA hdA, mul_inv_cancel_right])
    (fun u hu hua => by
      rw [← hCa]
      refine Subgroup.mem_inf.mpr ⟨hu, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc u * a = a * u * a⁻¹ * a := by rw [hua]
        _ = a * u := by group)
  set δx := a * x * a⁻¹ * x⁻¹ with hδxdef
  have hxc : x * c * x⁻¹ = c := by
    rw [h.commute_c_of_mem_inf hxRL, mul_inv_cancel_right]
  have hxd : x * d * x⁻¹ = d := by
    have := congrArg Subtype.val (h.isElemAbelian_inf.1.is_comm.comm ⟨x, hxRL⟩ ⟨d, hdRL⟩)
    simp only [Subgroup.coe_mul] at this
    rw [this, mul_inv_cancel_right]
  have hδxA : δx ∈ A := (Subgroup.zpowers_le.mpr hdA) hδx
  have hxa : x * a * x⁻¹ = δx⁻¹ * a := by rw [hδxdef]; group
  have hxA : ∀ u ∈ A, x * u * x⁻¹ * u⁻¹ ∈ Subgroup.zpowers d := by
    intro u hu
    rw [hA] at hu
    induction hu using Subgroup.closure_induction with
    | mem u hu =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl | rfl
      · rw [hxc, mul_inv_cancel]; exact Subgroup.one_mem _
      · rw [hxa, mul_inv_cancel_right]; exact Subgroup.inv_mem _ hδx
      · rw [hxd, mul_inv_cancel]; exact Subgroup.one_mem _
    | one => simp
    | mul u v hu hv ihu ihv =>
      have huA : u ∈ A := hA ▸ hu
      have hvA : v ∈ A := hA ▸ hv
      have h1 : x * (u * v) * x⁻¹ * (u * v)⁻¹ =
          (x * u * x⁻¹ * u⁻¹) * (u * (x * v * x⁻¹ * v⁻¹) * u⁻¹) := by group
      have h2 : u * (x * v * x⁻¹ * v⁻¹) * u⁻¹ = x * v * x⁻¹ * v⁻¹ := by
        have hmem : x * v * x⁻¹ * v⁻¹ ∈ A := (Subgroup.zpowers_le.mpr hdA) ihv
        rw [hcommA u huA _ hmem, mul_inv_cancel_right]
      rw [h1, h2]
      exact Subgroup.mul_mem _ ihu ihv
    | inv u hu ihu =>
      have huA : u ∈ A := hA ▸ hu
      have h1 : x * u⁻¹ * x⁻¹ * u⁻¹⁻¹ = u⁻¹ * (x * u * x⁻¹ * u⁻¹)⁻¹ * u := by group
      have hmem : (x * u * x⁻¹ * u⁻¹)⁻¹ ∈ A := A.inv_mem ((Subgroup.zpowers_le.mpr hdA) ihu)
      rw [h1, hcommA _ (A.inv_mem huA) _ hmem, inv_mul_cancel_right]
      exact Subgroup.inv_mem _ ihu
  have hxN : x ∈ Subgroup.normalizer (A : Set G) := by
    have : x⁻¹ ∈ Subgroup.normalizer (A : Set G) := by
      apply Sec11.mem_normalizer_of_forall_conj_mem
      intro u hu
      rw [inv_inv]
      have h1 := hxA u hu
      have h2 : x * u * x⁻¹ = (x * u * x⁻¹ * u⁻¹) * u := by group
      rw [h2]
      exact A.mul_mem ((Subgroup.zpowers_le.mpr hdA) h1) hu
    simpa using Subgroup.inv_mem _ this
  have hx1 : ∃ u ∈ A, x * u * x⁻¹ ≠ u := by
    refine ⟨a, haA, fun h1 => hδx1 ?_⟩
    rw [hxa] at h1
    have : δx⁻¹ = 1 := by
      calc δx⁻¹ = δx⁻¹ * a * a⁻¹ := by group
        _ = 1 := by rw [h1, mul_inv_cancel]
    exact inv_eq_one.mp this
  set y := k * x * k⁻¹ with hy
  set Dk := D.map (MulAut.conj k).toMonoidHom with hDk
  have hkcDk : k * c * k⁻¹ ∈ Dk := ⟨c, hcD, rfl⟩
  have heDk : e ∈ Dk := ⟨d, hdD, rfl⟩
  have hbDk : b ∈ Dk := Subgroup.zpowers_le.mpr hkcDk (hkc ▸ Subgroup.mem_zpowers b)
  have hcDk : c ∉ Dk := fun hc => hwD (mem_map_conj_iff.mp hc)
  have hyc0 : y * (k * c * k⁻¹) * y⁻¹ = k * c * k⁻¹ := by
    calc y * (k * c * k⁻¹) * y⁻¹ = k * (x * c * x⁻¹) * k⁻¹ := by rw [hy]; group
      _ = k * c * k⁻¹ := by rw [hxc]
  have hyb : y * b * y⁻¹ = b := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hkc ▸ Subgroup.mem_zpowers b :
      b ∈ Subgroup.zpowers (k * c * k⁻¹))
    have h1 := (conj_zpow (a := y) (b := k * c * k⁻¹) (i := m)).symm
    rw [← hm, h1, hyc0]
  have hye : y * e * y⁻¹ = e := by
    calc y * e * y⁻¹ = k * (x * d * x⁻¹) * k⁻¹ := by rw [hy, he]; group
      _ = e := by rw [hxd]
  set τ := x * a ^ j * x⁻¹ * (a ^ j)⁻¹ with hτdef
  have hδxa : δx * a = a * δx := h.comm hδxA haA
  have hτ : τ ∈ Subgroup.zpowers d ∧ τ ≠ 1 := by
    have hδx3 : δx ^ 3 = 1 := hexp _ hδxA
    rcases zpow_cases_of_pow_three ha3 j with hj | hj | hj
    · exfalso
      apply hwD
      rw [hwz, hj, one_mul]
      exact hzD
    · rw [hτdef, hj, hxa, mul_inv_cancel_right]
      exact ⟨Subgroup.inv_mem _ hδx, fun h1 => hδx1 (inv_eq_one.mp h1)⟩
    · have e1 : τ = δx⁻¹ * δx⁻¹ := by
        rw [hτdef, hj]
        have hx2 : x * a ^ 2 * x⁻¹ = (x * a * x⁻¹) ^ 2 := by rw [pow_two, pow_two]; group
        rw [hx2, hxa, pow_two]
        have h1 : δx⁻¹ * a * (δx⁻¹ * a) = δx⁻¹ * δx⁻¹ * (a * a) := by
          have h2 : a * δx⁻¹ = δx⁻¹ * a := by
            rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hδxa, inv_mul_cancel_left]
          calc δx⁻¹ * a * (δx⁻¹ * a) = δx⁻¹ * (a * δx⁻¹) * a := by group
            _ = δx⁻¹ * (δx⁻¹ * a) * a := by rw [h2]
            _ = δx⁻¹ * δx⁻¹ * (a * a) := by group
        rw [h1, show a * a = a ^ 2 from (pow_two a).symm, mul_inv_cancel_right]
      rw [e1]
      refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hδx) (Subgroup.inv_mem _ hδx), ?_⟩
      intro h1
      apply hδx1
      have h2 : δx⁻¹ * δx⁻¹ = δx := by
        rw [← mul_inv_rev, inv_eq_iff_mul_eq_one, ← pow_three']
        exact hδx3
      rw [← h2]
      exact h1
  have hxw : x * w * x⁻¹ = τ * w := by
    rw [hwz]
    have hxz : x * z = z * x := hzRL x hxRL
    calc x * (a ^ j * z) * x⁻¹ = x * a ^ j * x⁻¹ * (x * z * x⁻¹) := by group
      _ = x * a ^ j * x⁻¹ * z := by rw [hxz, mul_inv_cancel_right]
      _ = τ * (a ^ j * z) := by rw [hτdef]; group
  have hyc' : y * c * y⁻¹ = (k * τ * k⁻¹) * c := by
    calc y * c * y⁻¹ = k * (x * w * x⁻¹) * k⁻¹ := by rw [hy, hw]; group
      _ = k * (τ * w) * k⁻¹ := by rw [hxw]
      _ = (k * τ * k⁻¹) * c := by rw [hw]; group
  have hkτ : k * τ * k⁻¹ ∈ Subgroup.zpowers e := by
    rw [he, ← map_conj_zpowers]
    exact ⟨τ, hτ.1, rfl⟩
  have hyc : y * c * y⁻¹ * c⁻¹ ∈ Subgroup.zpowers e := by
    rw [hyc', mul_inv_cancel_right]
    exact hkτ
  have hyc1 : y * c * y⁻¹ ≠ c := by
    rw [hyc']
    intro h1
    apply hτ.2
    have h2 : k * τ * k⁻¹ = 1 := by
      calc k * τ * k⁻¹ = k * τ * k⁻¹ * c * c⁻¹ := by group
        _ = 1 := by rw [h1, mul_inv_cancel]
    calc τ = k⁻¹ * (k * τ * k⁻¹) * k := by group
      _ = 1 := by rw [h2]; group
  have hecb : e ∉ Subgroup.closure ({c, b} : Set G) := by
    intro hecb
    obtain ⟨i, j', hi, hj', hij⟩ := KFacts.exists_pow_mul_pow_of_mem_closure_pair
      (hcommA c hcA b hbA) hc3 (hexp b hbA) hecb
    have hciDk : c ^ i ∈ Dk := by
      have : c ^ i = e * (b ^ j')⁻¹ := by rw [hij]; group
      rw [this]
      exact Dk.mul_mem heDk (Dk.inv_mem (Dk.pow_mem hbDk _))
    interval_cases i
    · rw [pow_zero, one_mul] at hij
      apply hdc
      have h1 : e ∈ Subgroup.zpowers (k * c * k⁻¹) := by
        rw [hkc, hij]
        exact Subgroup.npow_mem_zpowers _ _
      rw [← map_conj_zpowers, he] at h1
      have h2 := mem_map_conj_iff.mp h1
      simpa [mul_assoc] using h2
    · rw [pow_one] at hciDk
      exact hcDk hciDk
    · apply hcDk
      have : c = (c ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hc3, one_mul, pow_one]
      rw [this]
      exact Dk.pow_mem hciDk 2
  have hgen : Subgroup.closure {c, b, e} = A :=
    Sec11.closure_triple_eq hexp h27 hcA hbA heA h.ne_one hbc hecb
  have hyN : y ∈ Subgroup.normalizer (A : Set G) := by
    have hle : Subgroup.closure ({c, b, e} : Set G) ≤ A.comap (MulAut.conj y).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      change y * u * y⁻¹ ∈ A
      rcases hu with rfl | rfl | rfl
      · rw [hyc']
        exact A.mul_mem ((Subgroup.zpowers_le.mpr heA) hkτ) hcA
      · rw [hyb]; exact hbA
      · rw [hye]; exact heA
    have : y⁻¹ ∈ Subgroup.normalizer (A : Set G) := by
      apply Sec11.mem_normalizer_of_forall_conj_mem
      intro u hu
      rw [inv_inv]
      exact hle (hgen ▸ hu)
    simpa using Subgroup.inv_mem _ this
  have hbcd : b ∉ Subgroup.closure ({c, d} : Set G) := fun h1 => hbD (hcdD h1)
  have hW1 : ∀ g : G, g * c * g⁻¹ ∈ Subgroup.closure ({c, d} : Set G) →
      g * c * g⁻¹ ∈ Subgroup.zpowers c := fun g hg => hW g (hcdD hg)
  have hW2 : ∀ g : G, g * c * g⁻¹ ∈ Subgroup.closure ({b, e} : Set G) →
      g * c * g⁻¹ ∈ Subgroup.zpowers b := by
    intro g hg
    have hbe : Subgroup.closure ({b, e} : Set G) ≤ Dk := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact hbDk
      · exact heDk
    have h1 := mem_map_conj_iff.mp (hbe hg)
    have h2 := hW (k⁻¹ * g) (by
      rw [show k⁻¹ * g * c * (k⁻¹ * g)⁻¹ = k⁻¹ * (g * c * g⁻¹) * k by group]
      exact h1)
    rw [← hkc, ← map_conj_zpowers]
    refine ⟨k⁻¹ * g * c * (k⁻¹ * g)⁻¹, h2, ?_⟩
    change k * (k⁻¹ * g * c * (k⁻¹ * g)⁻¹) * k⁻¹ = g * c * g⁻¹
    group
  exact false_of_lines hexp hcommA h27 hcA hbA heA hdA hgen hdc hbcd hxN hyN hxc hxd hxA hx1
    hyb hye hyc hyc1 ⟨g₀, hb⟩ hW1 hW2

end CFSG.RankThree.PartTwo.Sec10
