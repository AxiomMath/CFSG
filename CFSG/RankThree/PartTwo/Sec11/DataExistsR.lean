module

public import CFSG.RankThree.PartTwo.Sec11.Skeleton
public import CFSG.RankThree.PartTwo.Sec11.RFacts
public import CFSG.RankThree.PartTwo.Sec11.DataExistsMeta
public import CFSG.RankThree.PartTwo.Sec11.DataExistsOut

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

namespace RChoice

omit [Finite G] in
theorem exists_zpowers_eq_of_isCyclic {H : Subgroup G} (hH : IsCyclic H) :
    ∃ x : G, H = Subgroup.zpowers x := by
  obtain ⟨⟨x, hx⟩, hgen⟩ := IsCyclic.exists_generator (α := H)
  refine ⟨x, le_antisymm (fun y hy => ?_) (Subgroup.zpowers_le.mpr hx)⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨y, hy⟩)
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

omit [Finite G] in
theorem exists_pow_pow_eq_of_coprime {r : G} {u : ℕ} (hu : Nat.Coprime u (orderOf r)) :
    ∃ u' : ℕ, (r ^ u) ^ u' = r := by
  by_cases h1 : orderOf r = 1
  · rw [orderOf_eq_one_iff] at h1
    exact ⟨0, by rw [h1, one_pow, pow_zero]⟩
  by_cases h0 : orderOf r = 0
  · exact ⟨1, by
      rw [h0, Nat.coprime_zero_right] at hu
      rw [hu, pow_one, pow_one]⟩
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hu (by omega)
  refine ⟨m, ?_⟩
  rw [← pow_mul, ← pow_mod_orderOf, hm, pow_one]

end RChoice

open RChoice

section Std


variable {A : Subgroup G} {c : G} {L : Subgroup G} {a : G} {R Y : Subgroup G}

theorem Sec11Std.exists_zpowers_eq_inf_L (h : Sec11Std G A c L a R Y) :
    ∃ x : G, R ⊓ L = Subgroup.zpowers x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR3 : IsPGroup 3 R := h.isSylowOf.isPGroup
  set ι : (R ⊓ L : Subgroup G) →* L ⧸ aschbacherSolvableCore 3 L :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 L)).comp
      (Subgroup.inclusion (inf_le_right : R ⊓ L ≤ L)) with hι
  have hinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hy' : Subgroup.inclusion (inf_le_right : R ⊓ L ≤ L) y ∈ aschbacherSolvableCore 3 L :=
      (QuotientGroup.eq_one_iff _).mp hy
    obtain ⟨k, hk⟩ := (hR3.to_le inf_le_left) y
    have h1 := eq_one_of_mem_theta_of_pow_eq_one hy'
      (by rw [← map_pow, hk, map_one] : Subgroup.inclusion (inf_le_right : R ⊓ L ≤ L) y ^ 3 ^ k = 1)
    exact Subgroup.inclusion_injective _ (by rw [h1, map_one])
  have hP : IsPGroup 3 ι.range :=
    (hR3.to_le inf_le_left).of_surjective ι.rangeRestrict ι.rangeRestrict_surjective
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  have : IsCyclic (S : Subgroup (L ⧸ aschbacherSolvableCore 3 L)) :=
    isCyclic_sylow_three_of_isList1016 h.isList1016 S
  have : IsCyclic ι.range := Subgroup.isCyclic_of_le hS
  have hcyc : IsCyclic (R ⊓ L : Subgroup G) :=
    isCyclic_of_injective ι.rangeRestrict (MonoidHom.rangeRestrict_injective_iff.mpr hinj)
  exact exists_zpowers_eq_of_isCyclic hcyc

theorem Sec11Std.commute_s_x (h : Sec11Std G A c L a R Y) {x s : G}
    (hx : R ⊓ L = Subgroup.zpowers x)
    (hs : R ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers s) : s * x = x * s := by
  have hx' : x ∈ R ⊓ L := hx ▸ Subgroup.mem_zpowers x
  have hs' : s ∈ R ⊓ Sec4.thetaQuotCentralizer L := hs ▸ Subgroup.mem_zpowers s
  obtain ⟨-, hsθ⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hs'.2
  have h1 := hsθ x hx'.2
  have h2 : s * x * s⁻¹ * x⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
    have e : s * x * s⁻¹ * x⁻¹ = x * (x⁻¹ * (s * x * s⁻¹)) * x⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta L hx'.2) _).mp h1
  have h3 : s * x * s⁻¹ * x⁻¹ ∈ R :=
    R.mul_mem (R.mul_mem (R.mul_mem hs'.1 hx'.1) (R.inv_mem hs'.1)) (R.inv_mem hx'.1)
  have h4 := eq_one_of_mem_R_of_mem_theta h.isSylowOf.isPGroup h3 h2
  calc s * x = (s * x * s⁻¹ * x⁻¹) * (x * s) := by group
    _ = x * s := by rw [h4, one_mul]

theorem Sec11Std.eq_one_of_mem_inf (h : Sec11Std G A c L a R Y) {x s : G}
    (hx : R ⊓ L = Subgroup.zpowers x)
    (hs : R ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers s) {z : G}
    (hzx : z ∈ Subgroup.zpowers x) (hzs : z ∈ Subgroup.zpowers s) : z = 1 := by
  have hzRL : z ∈ R ⊓ L := hx ▸ hzx
  have hzC : z ∈ R ⊓ Sec4.thetaQuotCentralizer L := hs ▸ hzs
  obtain ⟨⟨z', hz'N⟩, hz'1, hz'z⟩ := hzC.2
  have hz'z' : z' = z := hz'z
  subst hz'z'
  have hρ : Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨z', Subgroup.le_normalizer hzRL.2⟩) = 1 :=
    MonoidHom.mem_ker.mp hz'1
  rw [thetaQuotMulAut_compAction_of_mem L hzRL.2] at hρ
  have hcen : ((⟨z', hzRL.2⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) ∈
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
    rw [Subgroup.mem_center_iff]
    intro q
    have := congrArg (fun φ : MulAut (L ⧸ aschbacherSolvableCore 3 L) => φ q) hρ
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    exact (mul_inv_eq_iff_eq_mul.mp this).symm
  rw [center_eq_bot_of_isList1016 h.isList1016, Subgroup.mem_bot] at hcen
  have hθ : (⟨z', hzRL.2⟩ : L) ∈ aschbacherSolvableCore 3 L := (QuotientGroup.eq_one_iff _).mp hcen
  exact eq_one_of_mem_R_of_mem_theta h.isSylowOf.isPGroup hzRL.1 ⟨⟨z', hzRL.2⟩, hθ, rfl⟩

theorem Sec11Std.inf_innerPreimage_eq (h : Sec11Std G A c L a R Y) {x s : G}
    (hxL : R ⊓ L = Subgroup.zpowers x)
    (hsC : R ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers s) :
    R ⊓ innerPreimage L = Subgroup.closure {s, x} := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx : x ∈ R ⊓ L := hxL ▸ Subgroup.mem_zpowers x
  have hs : s ∈ R ⊓ Sec4.thetaQuotCentralizer L := hsC ▸ Subgroup.mem_zpowers s
  set ρ := (Sec4.thetaQuotMulAut L).comp (Sec4.compAction L) with hρ
  apply le_antisymm
  swap
  · rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · refine ⟨hs.1, mem_innerPreimage_iff.mpr ⟨(Sec6.mem_thetaQuotCentralizer_iff.mp hs.2).1, ?_⟩⟩
      obtain ⟨⟨s', hs'N⟩, hs'1, hs's⟩ := hs.2
      have : (⟨s', hs'N⟩ : Subgroup.normalizer (L : Set G)) =
          ⟨y, (Sec6.mem_thetaQuotCentralizer_iff.mp hs.2).1⟩ := Subtype.ext hs's
      rw [this] at hs'1
      exact ⟨1, by rw [map_one]; exact (MonoidHom.mem_ker.mp hs'1).symm⟩
    · exact ⟨hx.1, mem_innerPreimage_iff.mpr ⟨Subgroup.le_normalizer hx.2,
        ⟨_, (thetaQuotMulAut_compAction_of_mem L hx.2).symm⟩⟩⟩
  rintro y ⟨hyR, hyI⟩
  obtain ⟨hyN, ⟨l, hl0⟩⟩ := mem_innerPreimage_iff.mp hyI
  have hl : MulAut.conj l = ρ ⟨y, hyN⟩ := hl0
  obtain ⟨Q, hQ⟩ := h.isSylowOf_inf_L
  set Q' := Q.mapSurjective (QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 L)) with hQ'
  have hZ := center_eq_bot_of_isList1016 h.isList1016
  have hτQ : ∀ q ∈ (Q' : Subgroup (L ⧸ aschbacherSolvableCore 3 L)),
      ρ ⟨y, hyN⟩ q ∈ (Q' : Subgroup (L ⧸ aschbacherSolvableCore 3 L)) := by
    intro q hq
    rw [hQ', Sylow.coe_mapSurjective] at hq ⊢
    obtain ⟨q₀, hq₀, rfl⟩ := hq
    have hq₀R : (q₀ : G) ∈ R ⊓ L := by
      rw [← hQ]
      exact ⟨q₀, hq₀, rfl⟩
    have hyq : y * (q₀ : G) * y⁻¹ ∈ R ⊓ L :=
      ⟨R.mul_mem (R.mul_mem hyR hq₀R.1) (R.inv_mem hyR),
        (Subgroup.mem_normalizer_iff.mp hyN _).mp q₀.2⟩
    rw [← hQ] at hyq
    obtain ⟨q₁, hq₁, hq₁eq⟩ := hyq
    refine ⟨q₁, hq₁, ?_⟩
    rw [QuotientGroup.mk'_apply, hρ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      Sec4.thetaQuotMulAut_mk]
    congr 1
    apply Subtype.ext
    exact hq₁eq
  have hlN : l ∈ Subgroup.normalizer
      ((Q' : Subgroup (L ⧸ aschbacherSolvableCore 3 L)) : Set _) := by
    refine Subgroup.mem_normalizer_fintype fun q hq => ?_
    have := hτQ q hq
    rw [← hl, MulAut.conj_apply] at this
    exact this
  obtain ⟨k, hk⟩ := h.isSylowOf.isPGroup ⟨y, hyR⟩
  have hyk : (⟨y, hyN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 ^ k = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val hk)
  have hlk : l ^ 3 ^ k = 1 := by
    have h1 : MulAut.conj (l ^ 3 ^ k) = 1 := by
      rw [map_pow, hl, ← map_pow, hyk, map_one]
    have h2 : l ^ 3 ^ k ∈ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
      rw [Subgroup.mem_center_iff]
      intro q
      have := congrArg (fun φ : MulAut (L ⧸ aschbacherSolvableCore 3 L) => φ q) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      exact (mul_inv_eq_iff_eq_mul.mp this).symm
    rw [hZ, Subgroup.mem_bot] at h2
    exact h2
  have hl3 : IsPGroup 3 (Subgroup.zpowers l) := by
    rintro ⟨w, hw⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    refine ⟨k, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hlk, one_zpow]
  have hsup := hl3.to_sup_of_normal_right' Q'.isPGroup' (Subgroup.zpowers_le.mpr hlN)
  have heq := Q'.is_maximal' hsup le_sup_right
  have hlQ : l ∈ (Q' : Subgroup (L ⧸ aschbacherSolvableCore 3 L)) := by
    rw [← heq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers l)
  rw [hQ', Sylow.coe_mapSurjective] at hlQ
  obtain ⟨q₀, hq₀, rfl⟩ := hlQ
  have hq₀x : (q₀ : G) ∈ Subgroup.zpowers x := by
    rw [← hxL, ← hQ]
    exact ⟨q₀, hq₀, rfl⟩
  have hq₀N : (q₀ : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer q₀.2
  have hu : y * (q₀ : G)⁻¹ ∈ R ⊓ Sec4.thetaQuotCentralizer L := by
    refine ⟨R.mul_mem hyR (R.inv_mem (by rw [← hxL] at hq₀x; exact hq₀x.1)), ?_⟩
    refine ⟨⟨y, hyN⟩ * (⟨(q₀ : G), hq₀N⟩ : Subgroup.normalizer (L : Set G))⁻¹,
      MonoidHom.mem_ker.mpr ?_, rfl⟩
    change ρ (⟨y, hyN⟩ * (⟨(q₀ : G), hq₀N⟩ : Subgroup.normalizer (L : Set G))⁻¹) = 1
    have hq : ρ ⟨(q₀ : G), hq₀N⟩ = MulAut.conj ((q₀ : L) : L ⧸ aschbacherSolvableCore 3 L) :=
      thetaQuotMulAut_compAction_of_mem L q₀.2
    rw [map_mul, map_inv, hq, ← hl, QuotientGroup.mk'_apply, mul_inv_cancel]
  rw [hsC] at hu
  have e : y = (y * (q₀ : G)⁻¹) * (q₀ : G) := by group
  rw [e]
  exact Subgroup.mul_mem _
    (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hu)
    (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hq₀x)

theorem Sec11Std.mul_ne_mul (h45 : Sec4.Item4_5) (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) (hA : A = Subgroup.closure {c, a, d}) {x : G}
    (hx : R ⊓ L = Subgroup.zpowers x) : a * x ≠ x * a := by
  intro hax
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hacd, -⟩ := h.not_mem_facts hdL hA
  obtain ⟨haN, ha3, -, -, -⟩ := basic_facts_of_conj h45 h hdL hA h.a_mem hacd
  set α := Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨a, haN⟩) with hα
  have hα3 : α ^ 3 = 1 := by
    have h1 : (⟨a, haN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using ha3)
    rw [hα, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hout := not_isInnerAut_of_not_mem_closure h.toHyp91 hdL hA h.a_mem hacd haN
  obtain ⟨Q, hQ⟩ := h.isSylowOf_inf_L
  set Q' := Q.mapSurjective (QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 L)) with hQ'
  obtain ⟨y, hy, hαy⟩ := exists_ne_of_sylow_of_isList1016 h.isList1016 hα3 hout Q'
  rw [hQ', Sylow.coe_mapSurjective] at hy
  obtain ⟨q, hq, rfl⟩ := hy
  apply hαy
  have hqx : (q : G) ∈ Subgroup.zpowers x := by
    rw [← hx, ← hQ]
    exact ⟨q, hq, rfl⟩
  have haq : a * (q : G) * a⁻¹ = q := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hqx
    rw [← hk, ← conj_zpow, show a * x * a⁻¹ = x by rw [hax, mul_inv_cancel_right]]
  rw [hα, QuotientGroup.mk'_apply, Sec4.thetaQuotMulAut_mk]
  congr 1
  apply Subtype.ext
  exact haq

theorem Sec11Std.exists_eq_closure (h45 : Sec4.Item4_5) (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) (hA : A = Subgroup.closure {c, a, d}) {x s : G}
    (hx : R ⊓ L = Subgroup.zpowers x)
    (hs : R ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers s) :
    ∃ r : G, R = Subgroup.closure {r, x, s} ∧ a ∈ Subgroup.closure {r, s} := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR3 : IsPGroup 3 R := h.isSylowOf.isPGroup
  have hRN : R ≤ Subgroup.normalizer (L : Set G) :=
    h.isSylowOf.le.trans (h.normalizer_le_normalizer_L h45)
  have hxRL : x ∈ R ⊓ L := hx ▸ Subgroup.mem_zpowers x
  have hsRC : s ∈ R ⊓ Sec4.thetaQuotCentralizer L := hs ▸ Subgroup.mem_zpowers s
  have haR : a ∈ R := le_R_of_hyp91 h.toHyp91 h.a_mem
  have hsx := h.commute_s_x hx hs
  have hV := h.inf_innerPreimage_eq hx hs
  set V := Subgroup.closure ({s, x} : Set G) with hVdef
  have hnx : ∀ y ∈ R, ∃ e : ℤ, y * x * y⁻¹ = x ^ e := by
    intro y hy
    have hm : y * x * y⁻¹ ∈ R ⊓ L := ⟨R.mul_mem (R.mul_mem hy hxRL.1) (R.inv_mem hy),
      (Subgroup.mem_normalizer_iff.mp (hRN hy) x).mp hxRL.2⟩
    rw [hx] at hm
    obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.mp hm
    exact ⟨e, he.symm⟩
  have hns : ∀ y ∈ R, ∃ e : ℤ, y * s * y⁻¹ = s ^ e := by
    intro y hy
    have hm : y * s * y⁻¹ ∈ R ⊓ Sec4.thetaQuotCentralizer L :=
      ⟨R.mul_mem (R.mul_mem hy hsRC.1) (R.inv_mem hy),
        Sec6.conj_mem_thetaQuotCentralizer hsRC.2 (hRN hy)⟩
    rw [hs] at hm
    obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.mp hm
    exact ⟨e, he.symm⟩
  have hVform : ∀ v ∈ V, ∃ i k : ℤ, v = x ^ i * s ^ k := by
    intro v hv
    have hv' : v ∈ Subgroup.closure ({x, s} : Set G) := by rwa [Set.pair_comm]
    exact Sec12.exists_zpow_mul_zpow_of_mem_closure_pair hsx.symm hv'
  have hxV : x ∈ V := Subgroup.subset_closure (by simp)
  have hsV : s ∈ V := Subgroup.subset_closure (by simp)
  have hconjV : ∀ y ∈ R, ∀ v ∈ V, y * v * y⁻¹ ∈ V := by
    intro y hy v hv
    obtain ⟨i, k, rfl⟩ := hVform v hv
    obtain ⟨e, he⟩ := hnx y hy
    obtain ⟨f, hf⟩ := hns y hy
    have e1 : y * (x ^ i * s ^ k) * y⁻¹ = (y * x * y⁻¹) ^ i * (y * s * y⁻¹) ^ k := by
      rw [conj_zpow, conj_zpow]
      group
    rw [e1, he, hf]
    exact V.mul_mem (V.zpow_mem (V.zpow_mem hxV e) i) (V.zpow_mem (V.zpow_mem hsV f) k)
  have hVc : ∀ v ∈ V, v * x = x * v := by
    intro v hv
    obtain ⟨i, k, rfl⟩ := hVform v hv
    have h1 : Commute (s ^ k) x := (Commute.zpow_left (show Commute s x from hsx) k)
    have h2 : Commute (x ^ i) x := Commute.zpow_left (Commute.refl x) i
    exact (h2.mul_left h1).eq
  set N := Subgroup.normalizer (L : Set G) with hNdef
  set ρ : N →* MulAut (L ⧸ aschbacherSolvableCore 3 L) :=
    (Sec4.thetaQuotMulAut L).comp (Sec4.compAction L) with hρ
  have hP : IsPGroup 3 ((R.subgroupOf N).map ρ) := (hR3.comap_subtype (K := N)).map ρ
  obtain ⟨σ₀, ⟨r₀', hr₀'R, rfl⟩, hgen⟩ := exists_forall_isInnerAut_of_isList1016 h.isList1016 hP
  have hr₀R : (r₀' : G) ∈ R := Subgroup.mem_subgroupOf.mp hr₀'R
  have hgenR : ∀ y ∈ R, ∃ i : ℕ, ((r₀' : G) ^ i)⁻¹ * y ∈ V := by
    intro y hy
    obtain ⟨i, hi⟩ := hgen (ρ ⟨y, hRN hy⟩) ⟨⟨y, hRN hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    refine ⟨i, ?_⟩
    rw [← hV]
    have hmN : ((r₀' : G) ^ i)⁻¹ * y ∈ N := N.mul_mem (N.inv_mem (N.pow_mem r₀'.2 i)) (hRN hy)
    refine ⟨R.mul_mem (R.inv_mem (R.pow_mem hr₀R i)) hy, mem_innerPreimage_iff.mpr ⟨hmN, ?_⟩⟩
    have e : (⟨((r₀' : G) ^ i)⁻¹ * y, hmN⟩ : N) = (r₀' ^ i)⁻¹ * ⟨y, hRN hy⟩ :=
      Subtype.ext (by simp)
    change ρ ⟨((r₀' : G) ^ i)⁻¹ * y, hmN⟩ ∈ _
    rw [e, map_mul, map_inv, map_pow]
    exact hi
  set r₀ : G := (r₀' : G) with hr₀def
  have hax := h.mul_ne_mul h45 hdL hA hx
  obtain ⟨j', hj'⟩ := hgenR a haR
  have hj'0 : j' ≠ 0 := by
    rintro rfl
    rw [pow_zero, inv_one, one_mul] at hj'
    exact hax (hVc a hj')
  obtain ⟨j, u, hu3, hj'eq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hj'0 3 (by norm_num)
  obtain ⟨N₀, hN₀⟩ := hR3 ⟨r₀, hr₀R⟩
  have hr₀N₀ : r₀ ^ 3 ^ N₀ = 1 := by simpa using congrArg Subtype.val hN₀
  have hcop : Nat.Coprime u (orderOf r₀) := by
    have h1 : orderOf r₀ ∣ 3 ^ N₀ := orderOf_dvd_of_pow_eq_one hr₀N₀
    have h2 : Nat.Coprime u (3 ^ N₀) := Nat.Coprime.pow_right _
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hu3))
    exact Nat.Coprime.coprime_dvd_right h1 h2
  obtain ⟨u', hu'⟩ := exists_pow_pow_eq_of_coprime hcop
  set r₁ := r₀ ^ u with hr₁def
  have hr₁R : r₁ ∈ R := R.pow_mem hr₀R u
  have hr₁a : ∃ v ∈ V, r₁ ^ 3 ^ j = v * a := by
    have e1 : r₁ ^ 3 ^ j = r₀ ^ j' := by rw [hr₁def, ← pow_mul, hj'eq, mul_comm]
    refine ⟨a * ((r₀ ^ j')⁻¹ * a)⁻¹ * a⁻¹, hconjV a haR _ (V.inv_mem hj'), ?_⟩
    rw [e1]
    group
  obtain ⟨v, hv, hv'⟩ := hr₁a
  obtain ⟨t₀, w₀, rfl⟩ := hVform v hv
  obtain ⟨l, hl⟩ := hnx r₁ hr₁R
  obtain ⟨κ, hκ⟩ := hns r₁ hr₁R
  obtain ⟨μ, hμ⟩ := hnx a haR
  obtain ⟨ν, hν⟩ := hns a haR
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hR3) ⟨x, hxRL.1⟩
  have hxm : orderOf x = 3 ^ m := by rw [← hm, Subgroup.orderOf_mk]
  obtain ⟨N₁, hN₁⟩ := hR3 ⟨r₁, hr₁R⟩
  have hr₁N : r₁ ^ 3 ^ N₁ = 1 := by simpa using congrArg Subtype.val hN₁
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have hxs : ∀ i k : ℤ, x ^ i = s ^ k → x ^ i = 1 := fun i k hik =>
    h.eq_one_of_mem_inf hx hs (Subgroup.zpow_mem_zpowers x i)
      (hik ▸ Subgroup.zpow_mem_zpowers s k)
  obtain ⟨t, ht⟩ := exists_mul_zpow_pow_eq_zpow_mul hxm hsx hxs hl hκ hμ hν hr₁N ha3 hax hv'
  set T := Subgroup.closure ({r₁ * x ^ t, x, s} : Set G) with hT
  have hrT : r₁ * x ^ t ∈ T := Subgroup.subset_closure (by simp)
  have hxT : x ∈ T := Subgroup.subset_closure (by simp)
  have hsT : s ∈ T := Subgroup.subset_closure (by simp)
  refine ⟨r₁ * x ^ t, le_antisymm ?_ ?_, ?_⟩
  · intro y hy
    obtain ⟨i, hi⟩ := hgenR y hy
    have hVT : V ≤ T := by
      rw [hVdef, Subgroup.closure_le]
      rintro z (rfl | rfl)
      exacts [hsT, hxT]
    have hr₁T : r₁ ∈ T := by
      have e : r₁ = r₁ * x ^ t * (x ^ t)⁻¹ := by group
      rw [e]
      exact T.mul_mem hrT (T.inv_mem (T.zpow_mem hxT t))
    have hr₀T : r₀ ∈ T := by
      rw [← hu']
      exact T.pow_mem hr₁T u'
    have e : y = r₀ ^ i * ((r₀ ^ i)⁻¹ * y) := by group
    rw [e]
    exact T.mul_mem (T.pow_mem hr₀T i) (hVT hi)
  · rw [Subgroup.closure_le]
    rintro z (rfl | rfl | rfl)
    · exact R.mul_mem hr₁R (R.zpow_mem hxRL.1 t)
    · exact hxRL.1
    · exact hsRC.1
  · have e : a = (s ^ w₀)⁻¹ * (r₁ * x ^ t) ^ 3 ^ j := by
      rw [ht]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.zpow_mem _
      (Subgroup.subset_closure (by simp)) _)) (Subgroup.pow_mem _
        (Subgroup.subset_closure (by simp)) _)

end Std

end CFSG.RankThree.PartTwo.Sec11
