module

public import CFSG.RankThree.PartTwo.Sec4.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item185Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

private theorem oTwoPAux_normal (p : ℕ) (H : Type*) [Group H] : (Sec4.oTwoP p H).Normal := by
  unfold Sec4.oTwoP
  exact Subgroup.Normal.comap CFSG.pCore_normal _

private theorem oTwoPAux_exists_pow_of_mem {p : ℕ} {H : Type*} [Group H] {x : H}
    (hx : x ∈ Sec4.oTwoP p H) : ∃ k : ℕ, x ^ p ^ k ∈ CFSG.pCore 2 H := by
  have hx' : QuotientGroup.mk' (CFSG.pCore 2 H) x ∈ CFSG.pCore p (H ⧸ CFSG.pCore 2 H) := hx
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := p) (G := H ⧸ CFSG.pCore 2 H)) ⟨_, hx'⟩
  refine ⟨k, (QuotientGroup.eq_one_iff _).mp ?_⟩
  rw [QuotientGroup.mk_pow]
  simpa using congrArg Subtype.val hk

private theorem oTwoPAux_le_of_pow_mem {p : ℕ} {H : Type*} [Group H] {R : Subgroup H}
    (hR : R.Normal) (h : ∀ r ∈ R, ∃ k : ℕ, r ^ p ^ k ∈ CFSG.pCore 2 H) :
    R ≤ Sec4.oTwoP p H := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 H) with hπ
  have hnorm : (R.map π).Normal := hR.map π (QuotientGroup.mk'_surjective (CFSG.pCore 2 H))
  have hpg : IsPGroup p ↥(R.map π) := by
    rintro ⟨g, hg⟩
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨k, hk⟩ := h r hr
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : π (r ^ p ^ k) = 1 := (QuotientGroup.eq_one_iff _).mpr hk
    rw [map_pow] at h1
    exact h1
  have hle : R.map π ≤ CFSG.pCore p (H ⧸ CFSG.pCore 2 H) := le_sSup ⟨hnorm, hpg⟩
  intro r hr
  exact hle (Subgroup.mem_map_of_mem π hr)

private theorem oTwoPAux_mem_of_equiv {p : ℕ} {H : Type*} [Group H] (σ : H ≃* H) {x : H}
    (hx : x ∈ Sec4.oTwoP p H) : σ x ∈ Sec4.oTwoP p H := by
  have hOσ : (CFSG.pCore 2 H).map σ.toMonoidHom = CFSG.pCore 2 H := CFSG.pCore_map_iso 2 σ
  set σ' : H ⧸ CFSG.pCore 2 H ≃* H ⧸ CFSG.pCore 2 H :=
    QuotientGroup.congr (CFSG.pCore 2 H) (CFSG.pCore 2 H) σ hOσ with hσ'
  have hP : (CFSG.pCore p (H ⧸ CFSG.pCore 2 H)).map σ'.toMonoidHom =
      CFSG.pCore p (H ⧸ CFSG.pCore 2 H) := CFSG.pCore_map_iso p σ'
  have hx' : QuotientGroup.mk' (CFSG.pCore 2 H) x ∈ CFSG.pCore p (H ⧸ CFSG.pCore 2 H) := hx
  have hcomm : QuotientGroup.mk' (CFSG.pCore 2 H) (σ x) =
      σ' (QuotientGroup.mk' (CFSG.pCore 2 H) x) := rfl
  show QuotientGroup.mk' (CFSG.pCore 2 H) (σ x) ∈ CFSG.pCore p (H ⧸ CFSG.pCore 2 H)
  rw [hcomm, ← hP]
  exact Subgroup.mem_map_of_mem σ'.toMonoidHom hx'

private theorem oTwoPAux_pCore_mem_of_equiv {p : ℕ} {H : Type*} [Group H] (σ : H ≃* H) {x : H}
    (hx : x ∈ CFSG.pCore p H) : σ x ∈ CFSG.pCore p H := by
  have h := CFSG.pCore_map_iso p σ
  rw [← h]
  exact Subgroup.mem_map_of_mem σ.toMonoidHom hx

private theorem oTwoPAux_conj_mem_of_normal {X Y : Subgroup G} (hYX : Y ≤ X)
    (hn : (Y.subgroupOf X).Normal) (x : X) {y : G} (hy : y ∈ Y) :
    (x : G) * y * (x : G)⁻¹ ∈ Y :=
  Subgroup.mem_subgroupOf.mp (hn.conj_mem ⟨y, hYX hy⟩ (Subgroup.mem_subgroupOf.mpr hy) x)

private def oTwoPAux_conjEquiv {X Y : Subgroup G} (hYX : Y ≤ X)
    (hn : (Y.subgroupOf X).Normal) (x : X) : Y ≃* Y where
  toFun y := ⟨(x : G) * y * (x : G)⁻¹, oTwoPAux_conj_mem_of_normal hYX hn x y.2⟩
  invFun y := ⟨((x⁻¹ : X) : G) * y * ((x⁻¹ : X) : G)⁻¹,
    oTwoPAux_conj_mem_of_normal hYX hn x⁻¹ y.2⟩
  left_inv y := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

private theorem oTwoPAux_conj_mem_map_of_stable {X Y : Subgroup G} (hYX : Y ≤ X)
    (hn : (Y.subgroupOf X).Normal) {S : Subgroup Y}
    (hS : ∀ σ : Y ≃* Y, ∀ s ∈ S, σ s ∈ S) (x : X) {g : G} (hg : g ∈ S.map Y.subtype) :
    (x : G) * g * (x : G)⁻¹ ∈ S.map Y.subtype := by
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hg
  exact Subgroup.mem_map.mpr ⟨oTwoPAux_conjEquiv hYX hn x s, hS _ s hs, rfl⟩

private theorem oTwoPAux_conj_mem_map_of_normal {X : Subgroup G} {S : Subgroup X} (hS : S.Normal)
    (x : X) {g : G} (hg : g ∈ S.map X.subtype) :
    (x : G) * g * (x : G)⁻¹ ∈ S.map X.subtype := by
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hg
  exact Subgroup.mem_map.mpr ⟨x * s * x⁻¹, hS.conj_mem s hs x, rfl⟩

private theorem oTwoPAux_le_pCore_subgroupOf {p : ℕ} {X S : Subgroup G}
    (hSn : (S.subgroupOf X).Normal) (hSp : IsPGroup p S) : S.subgroupOf X ≤ CFSG.pCore p ↥X :=
  le_sSup ⟨hSn, hSp.comap_subtype⟩

theorem oTwoP_le_of_normal {X Y : Subgroup G} (hYX : Y ≤ X) (hn : (Y.subgroupOf X).Normal) :
    (Sec4.oTwoP 3 ↥Y).map Y.subtype ≤ (Sec4.oTwoP 3 ↥X).map X.subtype := by
  have hP2 : ((CFSG.pCore 2 ↥Y).map Y.subtype).subgroupOf X ≤ CFSG.pCore 2 ↥X := by
    apply oTwoPAux_le_pCore_subgroupOf
    · refine ⟨fun n hn' g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn' ⊢
      exact oTwoPAux_conj_mem_map_of_stable hYX hn (S := CFSG.pCore 2 ↥Y)
        (fun σ s hs => oTwoPAux_pCore_mem_of_equiv σ hs) g hn'
    · exact (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)).map Y.subtype
  have hRn : (((Sec4.oTwoP 3 ↥Y).map Y.subtype).subgroupOf X).Normal := by
    refine ⟨fun n hn' g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn' ⊢
    exact oTwoPAux_conj_mem_map_of_stable hYX hn (S := Sec4.oTwoP 3 ↥Y)
      (fun σ s hs => oTwoPAux_mem_of_equiv σ hs) g hn'
  have hpow : ∀ n ∈ ((Sec4.oTwoP 3 ↥Y).map Y.subtype).subgroupOf X,
      ∃ k : ℕ, n ^ 3 ^ k ∈ CFSG.pCore 2 ↥X := by
    intro n hn'
    rw [Subgroup.mem_subgroupOf] at hn'
    obtain ⟨y, hy, hyn⟩ := Subgroup.mem_map.mp hn'
    obtain ⟨k, hk⟩ := oTwoPAux_exists_pow_of_mem hy
    refine ⟨k, hP2 ?_⟩
    rw [Subgroup.mem_subgroupOf]
    refine Subgroup.mem_map.mpr ⟨y ^ 3 ^ k, hk, ?_⟩
    rw [map_pow, hyn, Subgroup.coe_pow]
  have hle := oTwoPAux_le_of_pow_mem hRn hpow
  intro g hg
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
  have hz : (⟨(y : G), hYX y.2⟩ : ↥X) ∈ ((Sec4.oTwoP 3 ↥Y).map Y.subtype).subgroupOf X :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)
  exact Subgroup.mem_map.mpr ⟨_, hle hz, rfl⟩

theorem inf_oTwoP_le {X Y : Subgroup G} (hYX : Y ≤ X) :
    (Sec4.oTwoP 3 ↥X).map X.subtype ⊓ Y ≤ (Sec4.oTwoP 3 ↥Y).map Y.subtype := by
  have hRn : ((((Sec4.oTwoP 3 ↥X).map X.subtype) ⊓ Y).subgroupOf Y).Normal := by
    refine ⟨fun n hn' g => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hn' ⊢
    obtain ⟨hnO, -⟩ := hn'
    refine ⟨?_, (g * n * g⁻¹ : ↥Y).2⟩
    exact oTwoPAux_conj_mem_map_of_normal (oTwoPAux_normal 3 ↥X) ⟨(g : G), hYX g.2⟩ hnO
  have hQn : ((((CFSG.pCore 2 ↥X).map X.subtype) ⊓ Y).subgroupOf Y).Normal := by
    refine ⟨fun n hn' g => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hn' ⊢
    obtain ⟨hnP, -⟩ := hn'
    refine ⟨?_, (g * n * g⁻¹ : ↥Y).2⟩
    exact oTwoPAux_conj_mem_map_of_normal CFSG.pCore_normal ⟨(g : G), hYX g.2⟩ hnP
  have hQ2 : ((CFSG.pCore 2 ↥X).map X.subtype ⊓ Y).subgroupOf Y ≤ CFSG.pCore 2 ↥Y :=
    oTwoPAux_le_pCore_subgroupOf hQn
      ((CFSG.pCore_isPGroup (p := 2) (G := ↥X)).map X.subtype |>.to_le inf_le_left)
  have hpow : ∀ n ∈ (((Sec4.oTwoP 3 ↥X).map X.subtype) ⊓ Y).subgroupOf Y,
      ∃ k : ℕ, n ^ 3 ^ k ∈ CFSG.pCore 2 ↥Y := by
    intro n hn'
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hn'
    obtain ⟨hnO, -⟩ := hn'
    obtain ⟨n', hn'O, hn'eq⟩ := Subgroup.mem_map.mp hnO
    obtain ⟨k, hk⟩ := oTwoPAux_exists_pow_of_mem hn'O
    refine ⟨k, hQ2 ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    refine ⟨Subgroup.mem_map.mpr ⟨n' ^ 3 ^ k, hk, ?_⟩, (n ^ 3 ^ k).2⟩
    rw [map_pow, hn'eq, Subgroup.coe_pow]
  have hle := oTwoPAux_le_of_pow_mem hRn hpow
  intro g hg
  obtain ⟨hgO, hgY⟩ := Subgroup.mem_inf.mp hg
  have hmem : (⟨g, hgY⟩ : ↥Y) ∈ Sec4.oTwoP 3 ↥Y :=
    hle (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hgO, hgY⟩))
  exact Subgroup.mem_map.mpr ⟨⟨g, hgY⟩, hmem, rfl⟩

theorem le_oTwoP_of_normal_closure {Y B N : Subgroup G} (hBY : B ≤ Y) (hNY : N ≤ Y)
    (hN : IsPGroup 2 N) (hNn : (N.subgroupOf Y).Normal) (hB3 : IsPGroup 3 B)
    (hBN : ((B ⊔ N).subgroupOf Y).Normal) :
    B ≤ (Sec4.oTwoP 3 ↥Y).map Y.subtype := by
  haveI : (N.subgroupOf Y).Normal := hNn
  have hNle : N.subgroupOf Y ≤ CFSG.pCore 2 ↥Y := oTwoPAux_le_pCore_subgroupOf hNn hN
  have hpow : ∀ r ∈ (B ⊔ N).subgroupOf Y, ∃ k : ℕ, r ^ 3 ^ k ∈ CFSG.pCore 2 ↥Y := by
    intro r hr
    have hr' : r ∈ B.subgroupOf Y ⊔ N.subgroupOf Y := by
      rw [← Subgroup.subgroupOf_sup hBY hNY]
      exact hr
    obtain ⟨b, hb, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hr'
    obtain ⟨j, hj⟩ := (hB3.comap_subtype (K := Y)) ⟨b, hb⟩
    have hbj : b ^ 3 ^ j = 1 := by
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using congrArg Subtype.val hj
    refine ⟨j, hNle ?_⟩
    refine (QuotientGroup.eq_one_iff _).mp ?_
    rw [QuotientGroup.mk_pow, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn,
      mul_one, ← QuotientGroup.mk_pow, hbj, QuotientGroup.mk_one]
  have hle := oTwoPAux_le_of_pow_mem hBN hpow
  intro b hb
  have hbY : b ∈ Y := hBY hb
  have hmem : (⟨b, hbY⟩ : ↥Y) ∈ Sec4.oTwoP 3 ↥Y :=
    hle (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hb))
  exact Subgroup.mem_map.mpr ⟨⟨b, hbY⟩, hmem, rfl⟩

theorem oTwoP_map_le_of_surjective {Y Z : Type} [Group Y] [Group Z] [Finite Y] (f : Y →* Z)
    (hf : Function.Surjective f) : (Sec4.oTwoP 3 Y).map f ≤ Sec4.oTwoP 3 Z := by
  refine oTwoPAux_le_of_pow_mem ((oTwoPAux_normal 3 Y).map f hf) ?_
  rintro r ⟨x, hx, rfl⟩
  obtain ⟨k, hk⟩ := oTwoPAux_exists_pow_of_mem hx
  refine ⟨k, ?_⟩
  rw [← map_pow]
  have hle : (CFSG.pCore 2 Y).map f ≤ CFSG.pCore 2 Z :=
    le_sSup ⟨(CFSG.pCore_normal (p := 2) (G := Y)).map f hf,
      (CFSG.pCore_isPGroup (p := 2) (G := Y)).map f⟩
  exact hle (Subgroup.mem_map_of_mem f hk)

end CFSG.RankThree.PartTwo.Sec18.Item185Proof
