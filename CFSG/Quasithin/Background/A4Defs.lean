module

public import CFSG.Quasithin.Background.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type*} [Group G]

@[expose] def oTwoUpper (X : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | x ∈ X ∧ Odd (orderOf x)}

theorem oTwoUpper_le (X : Subgroup G) : oTwoUpper X ≤ X :=
  (Subgroup.closure_le X).mpr fun _ hx => hx.1

theorem oTwoUpper_mono {X Y : Subgroup G} (h : X ≤ Y) : oTwoUpper X ≤ oTwoUpper Y :=
  Subgroup.closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

theorem mem_oTwoUpper_of_odd {X : Subgroup G} {x : G} (hx : x ∈ X) (ho : Odd (orderOf x)) :
    x ∈ oTwoUpper X :=
  Subgroup.subset_closure ⟨hx, ho⟩

namespace A4

theorem mem_zpowers_pow_of_coprime {x : G} {n : ℕ} (h : Nat.Coprime n (orderOf x)) :
    x ∈ Subgroup.zpowers (x ^ n) := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr h
  refine ⟨a, ?_⟩
  have hxo : x ^ (orderOf x : ℤ) = 1 := by rw [zpow_natCast, pow_orderOf_eq_one]
  have h1 : x ^ (a * n + b * (orderOf x : ℤ)) = x := by rw [hab, zpow_one]
  have h2 : x ^ (a * n + b * (orderOf x : ℤ)) = x ^ (a * n) := by
    rw [zpow_add, mul_comm b, zpow_mul x _ b, hxo, one_zpow, mul_one]
  calc (x ^ n) ^ a = x ^ (a * n) := by rw [← zpow_natCast, ← zpow_mul, mul_comm]
    _ = x := h2.symm.trans h1

end A4

theorem conj_mem_oTwoUpper {X : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G))
    {y : G} (hy : y ∈ oTwoUpper X) : g * y * g⁻¹ ∈ oTwoUpper X := by
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    refine mem_oTwoUpper_of_odd ((Subgroup.mem_normalizer_iff.mp hg x).mp hx.1) ?_
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hx.2
  | one => simp
  | mul x y _ _ ihx ihy =>
    simpa [mul_assoc] using (oTwoUpper X).mul_mem ihx ihy
  | inv x _ ih =>
    simpa [mul_assoc] using (oTwoUpper X).inv_mem ih

theorem normalizer_le_normalizer_oTwoUpper (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (oTwoUpper X : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_oTwoUpper hg hx, fun hx => ?_⟩
  have := conj_mem_oTwoUpper (Subgroup.inv_mem _ hg) hx
  simpa [mul_assoc] using this

theorem le_normalizer_oTwoUpper (X : Subgroup G) :
    X ≤ Subgroup.normalizer (oTwoUpper X : Set G) :=
  Subgroup.le_normalizer.trans (normalizer_le_normalizer_oTwoUpper X)

theorem oTwoUpper_le_of_pow_mem {X N : Subgroup G} (h : ∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k ∈ N) :
    oTwoUpper X ≤ N := by
  refine (Subgroup.closure_le N).mpr fun x hx => ?_
  obtain ⟨k, hk⟩ := h x hx.1
  have hcop : Nat.Coprime (2 ^ k) (orderOf x) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hx.2)
  exact (Subgroup.zpowers_le.mpr hk) (A4.mem_zpowers_pow_of_coprime hcop)

theorem exists_pow_mem_oTwoUpper [Finite G] (X : Subgroup G) {x : G} (hx : x ∈ X) :
    ∃ k : ℕ, x ^ 2 ^ k ∈ oTwoUpper X := by
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  refine ⟨k, mem_oTwoUpper_of_odd (X.pow_mem hx _) ?_⟩
  have h2k : (2 ^ k : ℕ) ≠ 0 := by positivity
  rw [orderOf_pow' _ h2k, hkm, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ (by positivity)]
  exact hm

theorem eq_oTwoUpper_of_pow_mem {H X : Subgroup G} (hHX : H ≤ X)
    (h : ∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k ∈ H) (hH : H = oTwoUpper H) : H = oTwoUpper X :=
  le_antisymm (hH ▸ oTwoUpper_mono hHX) (oTwoUpper_le_of_pow_mem h)

theorem oTwoUpper_map [Finite G] {G' : Type*} [Group G'] (f : G →* G') (X : Subgroup G) :
    oTwoUpper (X.map f) = (oTwoUpper X).map f := by
  apply le_antisymm
  · refine oTwoUpper_le_of_pow_mem fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper X hx
    exact ⟨k, ⟨_, hk, by rw [map_pow]⟩⟩
  · rw [oTwoUpper, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, ⟨hx, ho⟩, rfl⟩
    exact mem_oTwoUpper_of_odd (Subgroup.mem_map_of_mem f hx) (ho.of_dvd_nat (orderOf_map_dvd f x))

namespace A4

theorem exists_pow_mul_eq {H : Subgroup G} {x r : G} (hx : x ∈ H)
    (hr : r ∈ Subgroup.normalizer (H : Set G)) (n : ℕ) :
    ∃ x' ∈ H, (x * r) ^ n = x' * r ^ n := by
  induction n with
  | zero => exact ⟨1, H.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨x', hx', h⟩ := ih
    have hconj : r ^ n * x * (r ^ n)⁻¹ ∈ H :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hr n) x).mp hx
    refine ⟨x' * (r ^ n * x * (r ^ n)⁻¹), H.mul_mem hx' hconj, ?_⟩
    rw [pow_succ, h, pow_succ]
    group

end A4

namespace A4

theorem subnormal_le {H K : Subgroup G} (h : IsSubnormal H K) : H ≤ K :=
  h.le

theorem subnormal_trans {H M K : Subgroup G} (h₁ : IsSubnormal H M) (h₂ : IsSubnormal M K) :
    IsSubnormal H K :=
  h₁.trans h₂

theorem subnormal_of_normal {H K : Subgroup G} (hle : H ≤ K) (hN : (H.subgroupOf K).Normal) :
    IsSubnormal H K :=
  IsSubnormal.step hle hN (IsSubnormal.refl K)

theorem subnormal_inf_right {H K : Subgroup G} (h : IsSubnormal H K) :
    ∀ {L : Subgroup G}, L ≤ K → IsSubnormal (H ⊓ L) L :=
  fun hL => h.inf_of_le hL

theorem subnormal_of_le_of_le {H K L : Subgroup G} (h : IsSubnormal H K) (hHL : H ≤ L)
    (hLK : L ≤ K) : IsSubnormal H L := by
  simpa [inf_eq_left.mpr hHL] using subnormal_inf_right h hLK

theorem pCoreOf_le_of_subnormal (p : ℕ) [Fact p.Prime] [Finite G] {H K : Subgroup G}
    (h : IsSubnormal H K) : pCoreOf p H ≤ pCoreOf p K := by
  induction h with
  | refl => exact le_rfl
  | @step H M K hle hN _ ih =>
    refine le_trans ?_ ih
    refine le_pCoreOf_of_le_normalizer p ((pCoreOf_le p H).trans hle) ?_ (pCoreOf_isPGroup p H)
    intro m hm
    have hmH : m ∈ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hN hm
    exact normalizer_le_normalizer_pCoreOf p H hmH


theorem subgroupOf_map_subtype' (H : Subgroup G) (K : Subgroup H) :
    (K.map H.subtype).subgroupOf H = K :=
  Subgroup.comap_map_eq_self_of_injective H.subtype_injective K

theorem isPGroup_subgroupOf_of_le {S H : Subgroup G} (hSH : S ≤ H) (hS : IsPGroup 2 S) :
    IsPGroup 2 (S.subgroupOf H) :=
  hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm

@[expose] noncomputable def toSylow {S H : Subgroup G} (h : IsSylowTwoOf S H) : Sylow 2 H :=
  IsPGroup.toSylow (P := S.subgroupOf H) (isPGroup_subgroupOf_of_le h.1 h.2.1) h.2.2

theorem toSylow_coe {S H : Subgroup G} (h : IsSylowTwoOf S H) :
    ((toSylow h : Sylow 2 H) : Subgroup H) = S.subgroupOf H := rfl

section Finite

variable [Finite G]

theorem isSylowTwoOf_map (H : Subgroup G) (Q : Sylow 2 H) :
    IsSylowTwoOf ((Q : Subgroup H).map H.subtype) H := by
  refine ⟨Subgroup.map_subtype_le _, Q.isPGroup'.map H.subtype, ?_⟩
  rw [subgroupOf_map_subtype']
  exact Q.not_dvd_index

theorem isSylowTwoOf_iff_maximal {S H : Subgroup G} :
    IsSylowTwoOf S H ↔ S ≤ H ∧ IsPGroup 2 S ∧
      ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P → S ≤ P → P ≤ S := by
  constructor
  · rintro ⟨hSH, hS, hidx⟩
    refine ⟨hSH, hS, fun P hPH hP hSP => ?_⟩
    have h1 : S.relIndex P * P.relIndex H = S.relIndex H :=
      Subgroup.relIndex_mul_relIndex S P H hSP hPH
    obtain ⟨n, hn⟩ := hP.index (S.subgroupOf P)
    have hdvd : S.relIndex P ∣ S.relIndex H := ⟨_, h1.symm⟩
    have hn0 : n = 0 := by
      by_contra hne
      refine hidx (dvd_trans ?_ hdvd)
      rw [Subgroup.relIndex, hn]
      exact dvd_pow_self 2 hne
    rw [hn0, pow_zero] at hn
    exact (Subgroup.relIndex_eq_one.mp hn)
  · rintro ⟨hSH, hS, hmax⟩
    refine ⟨hSH, hS, ?_⟩
    let Q : Sylow 2 H :=
      { toSubgroup := S.subgroupOf H
        isPGroup' := isPGroup_subgroupOf_of_le hSH hS
        is_maximal' := fun {P'} hP' hle => by
          refine le_antisymm (fun p hp => ?_) hle
          have hP'G : IsPGroup 2 (P'.map H.subtype) := hP'.map H.subtype
          have hSP : S ≤ P'.map H.subtype := by
            intro s hs
            exact ⟨⟨s, hSH hs⟩, hle hs, rfl⟩
          have := hmax _ (Subgroup.map_subtype_le _) hP'G hSP ⟨p, hp, rfl⟩
          exact this }
    exact Q.not_dvd_index

theorem exists_isSylowTwoOf_ge {P H : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup 2 P) :
    ∃ S, IsSylowTwoOf S H ∧ P ≤ S := by
  obtain ⟨Q, hQ⟩ := (isPGroup_subgroupOf_of_le hPH hP).exists_le_sylow
  exact ⟨(Q : Subgroup H).map H.subtype, isSylowTwoOf_map H Q,
    fun p hp => ⟨⟨p, hPH hp⟩, hQ hp, rfl⟩⟩

theorem isSylowTwoOf_mono {S H K : Subgroup G} (hS : IsSylowTwoOf S H) (hSK : S ≤ K)
    (hKH : K ≤ H) : IsSylowTwoOf S K := by
  rw [isSylowTwoOf_iff_maximal] at hS ⊢
  exact ⟨hSK, hS.2.1, fun P hPK hP hSP => hS.2.2 P (hPK.trans hKH) hP hSP⟩

theorem exists_isSylowTwoOf_le_of_odd {K H : Subgroup G} (hKH : K ≤ H)
    (hodd : Odd (K.relIndex H)) : ∃ S, IsSylowTwoOf S H ∧ S ≤ K := by
  obtain ⟨S, hS, -⟩ := exists_isSylowTwoOf_ge (P := ⊥) (H := K) bot_le
    (IsPGroup.of_card (n := 0) (by simp))
  refine ⟨S, ⟨hS.1.trans hKH, hS.2.1, ?_⟩, hS.1⟩
  have h : S.relIndex H = S.relIndex K * K.relIndex H :=
    (Subgroup.relIndex_mul_relIndex S K H hS.1 hKH).symm
  have h1 : Odd (S.relIndex K) :=
    Nat.not_even_iff_odd.mp fun he => hS.2.2 (even_iff_two_dvd.mp he)
  show ¬ 2 ∣ S.relIndex H
  rw [h]
  have : Odd (S.relIndex K * K.relIndex H) := h1.mul hodd
  intro hd
  exact (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr hd)

end Finite

theorem le_of_normal_of_isSylowTwoOf {S H N : Subgroup G} (hS : IsSylowTwoOf S H) (hNH : N ≤ H)
    (hN : (N.subgroupOf H).Normal) (hp : IsPGroup 2 N) : N ≤ S := by
  have := (isPGroup_subgroupOf_of_le hNH hp).le_sylow_of_normal (toSylow hS)
  intro n hn
  exact this (show (⟨n, hNH hn⟩ : H) ∈ N.subgroupOf H from hn)

theorem relIndex_sup_eq_of_le_normalizer' {D T : Subgroup G}
    (hT : T ≤ Subgroup.normalizer (D : Set G)) : D.relIndex (T ⊔ D) = D.relIndex T := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hT
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hT
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient T D hT).toEquiv.symm

variable [Finite G]

theorem isSylowTwoOf_inf_normal {S H N : Subgroup G} (hS : IsSylowTwoOf S H) (hNH : N ≤ H)
    (hnorm : H ≤ Subgroup.normalizer (N : Set G)) : IsSylowTwoOf (S ⊓ N) N := by
  refine ⟨inf_le_right, hS.2.1.to_inf_left, ?_⟩
  have hSN : S ≤ Subgroup.normalizer (N : Set G) := hS.1.trans hnorm
  have h1 : N.relIndex (S ⊔ N) = N.relIndex S := relIndex_sup_eq_of_le_normalizer' hSN
  have h2 : N.relIndex (S ⊔ N) * Nat.card ↥(N ⊓ (S ⊔ N)) = Nat.card ↥(S ⊔ N) :=
    Subgroup.relIndex_mul_card _ _
  have h3 : N.relIndex S * Nat.card ↥(N ⊓ S) = Nat.card ↥S := Subgroup.relIndex_mul_card _ _
  have h4 : (S ⊓ N).relIndex N * Nat.card ↥(S ⊓ N ⊓ N) = Nat.card ↥N :=
    Subgroup.relIndex_mul_card _ _
  have h5 : S.relIndex H * Nat.card ↥(S ⊓ H) = Nat.card ↥H := Subgroup.relIndex_mul_card _ _
  rw [inf_eq_left.mpr (le_sup_right : N ≤ S ⊔ N)] at h2
  rw [inf_comm N S] at h3
  rw [inf_eq_left.mpr (inf_le_right : S ⊓ N ≤ N)] at h4
  rw [inf_eq_left.mpr hS.1] at h5
  have hb : 0 < Nat.card ↥S := Nat.card_pos
  have hdvd : Nat.card ↥(S ⊔ N) ∣ Nat.card ↥H :=
    Subgroup.card_dvd_of_le (sup_le hS.1 hNH)
  have h6 : Nat.card ↥(S ⊔ N) = (S ⊓ N).relIndex N * Nat.card ↥S := by
    rw [← h2, h1, ← h3]
    calc N.relIndex S * Nat.card ↥N
        = N.relIndex S * ((S ⊓ N).relIndex N * Nat.card ↥(S ⊓ N)) := by rw [h4]
      _ = (S ⊓ N).relIndex N * (N.relIndex S * Nat.card ↥(S ⊓ N)) := by ring
  rw [h6, ← h5] at hdvd
  have h7 : (S ⊓ N).relIndex N ∣ S.relIndex H :=
    Nat.dvd_of_mul_dvd_mul_right hb (by simpa [mul_comm] using hdvd)
  intro h2dvd
  exact hS.2.2 (dvd_trans h2dvd h7)

open scoped Pointwise in
theorem exists_conj_of_isSylowTwoOf {S S' H : Subgroup G} (hS : IsSylowTwoOf S H)
    (hS' : IsSylowTwoOf S' H) : ∃ h ∈ H, ∀ x : G, x ∈ S' ↔ h⁻¹ * x * h ∈ S := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥H) (toSylow hS) (toSylow hS')
  have hg' : MulAut.conj g • ((toSylow hS : Sylow 2 H) : Subgroup H) =
      ((toSylow hS' : Sylow 2 H) : Subgroup H) := by
    rw [← Sylow.coe_subgroup_smul (g := g), hg]
  refine ⟨g, g.2, fun x => ?_⟩
  constructor
  · intro hx
    have hxH : x ∈ H := hS'.1 hx
    have : (⟨x, hxH⟩ : H) ∈ ((toSylow hS' : Sylow 2 H) : Subgroup H) := hx
    rw [← hg', Subgroup.mem_smul_pointwise_iff_exists] at this
    obtain ⟨s, hs, hsx⟩ := this
    have : (g : G)⁻¹ * x * g = (s : G) := by
      have h2 : ((MulAut.conj g • s : H) : G) = x := congrArg Subtype.val hsx
      simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h2
      rw [← h2]; group
    rw [this]
    exact hs
  · intro hx
    have hxH : (g : G)⁻¹ * x * g ∈ H := hS.1 hx
    have hxH' : x ∈ H := by
      have := H.mul_mem (H.mul_mem g.2 hxH) (H.inv_mem g.2)
      simpa [mul_assoc] using this
    have : (⟨x, hxH'⟩ : H) ∈ ((toSylow hS' : Sylow 2 H) : Subgroup H) := by
      rw [← hg', Subgroup.mem_smul_pointwise_iff_exists]
      refine ⟨⟨(g : G)⁻¹ * x * g, hxH⟩, hx, ?_⟩
      apply Subtype.ext
      simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    exact this

omit [Finite G] in
theorem subnormal_map {G' : Type*} [Group G'] (f : G →* G') {H K : Subgroup G}
    (h : IsSubnormal H K) : IsSubnormal (H.map f) (K.map f) :=
  h.map f

omit [Finite G] in
theorem subnormal_comap {G' : Type*} [Group G'] (f : G' →* G) {H K : Subgroup G}
    (h : IsSubnormal H K) : IsSubnormal (H.comap f) (K.comap f) :=
  h.comap f

omit [Finite G] in
theorem subnormal_subgroupOf (L : Subgroup G) {H K : Subgroup G} (h : IsSubnormal H K) :
    IsSubnormal (H.subgroupOf L) (K.subgroupOf L) :=
  subnormal_comap L.subtype h

end A4

@[expose] def centralizerSection (M X Z : Subgroup G) : Subgroup G where
  carrier := {m | m ∈ M ∧ m ∈ Subgroup.normalizer (X : Set G) ∧
    m ∈ Subgroup.normalizer (Z : Set G) ∧ ∀ x ∈ X, x * m * x⁻¹ * m⁻¹ ∈ Z}
  one_mem' := ⟨M.one_mem, Subgroup.one_mem _, Subgroup.one_mem _, fun x _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨haM, haX, haZ, ha⟩ ⟨hbM, hbX, hbZ, hb⟩
    refine ⟨M.mul_mem haM hbM, Subgroup.mul_mem _ haX hbX, Subgroup.mul_mem _ haZ hbZ, fun x hx => ?_⟩
    have h1 := ha x hx
    have h2 := (Subgroup.mem_normalizer_iff.mp haZ _).mp (hb x hx)
    have : x * (a * b) * x⁻¹ * (a * b)⁻¹ =
        (x * a * x⁻¹ * a⁻¹) * (a * (x * b * x⁻¹ * b⁻¹) * a⁻¹) := by group
    rw [this]
    exact Z.mul_mem h1 h2
  inv_mem' := by
    rintro a ⟨haM, haX, haZ, ha⟩
    refine ⟨M.inv_mem haM, Subgroup.inv_mem _ haX, Subgroup.inv_mem _ haZ, fun x hx => ?_⟩
    have h1 := Z.inv_mem (ha x hx)
    have h2 := (Subgroup.mem_normalizer_iff''.mp haZ _).mp h1
    have : x * a⁻¹ * x⁻¹ * (a⁻¹)⁻¹ = a⁻¹ * (x * a * x⁻¹ * a⁻¹)⁻¹ * a := by group
    rw [this]
    exact h2

theorem mem_centralizerSection {M X Z : Subgroup G} {m : G} :
    m ∈ centralizerSection M X Z ↔ m ∈ M ∧ m ∈ Subgroup.normalizer (X : Set G) ∧
      m ∈ Subgroup.normalizer (Z : Set G) ∧ ∀ x ∈ X, x * m * x⁻¹ * m⁻¹ ∈ Z := Iff.rfl

theorem centralizerSection_le_left (M X Z : Subgroup G) : centralizerSection M X Z ≤ M :=
  fun _ h => h.1

theorem centralizerSection_le_normalizer_left (M X Z : Subgroup G) :
    centralizerSection M X Z ≤ Subgroup.normalizer (X : Set G) := fun _ h => h.2.1

theorem centralizerSection_le_normalizer_right (M X Z : Subgroup G) :
    centralizerSection M X Z ≤ Subgroup.normalizer (Z : Set G) := fun _ h => h.2.2.1

theorem centralizerSection_mono {M M' : Subgroup G} (h : M ≤ M') (X Z : Subgroup G) :
    centralizerSection M X Z ≤ centralizerSection M' X Z :=
  fun _ hm => ⟨h hm.1, hm.2⟩

namespace A4

theorem mem_normalizer_of_conj_mem [Finite G] {K : Subgroup G} {m : G}
    (h : ∀ k ∈ K, m * k * m⁻¹ ∈ K) : m ∈ Subgroup.normalizer (K : Set G) := by
  have hinj : Function.Injective (fun k : K => (⟨m * k * m⁻¹, h k k.2⟩ : K)) := by
    intro a b hab
    have := congrArg Subtype.val hab
    simp only [mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  have hsurj := Finite.injective_iff_surjective.mp hinj
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  obtain ⟨k, hk⟩ := hsurj ⟨m * x * m⁻¹, hx⟩
  have := congrArg Subtype.val hk
  simp only [mul_left_inj, mul_right_inj] at this
  rw [← this]
  exact k.2

end A4

theorem mem_centralizerSection_iff_of_le [Finite G] {M X Z : Subgroup G} (hZX : Z ≤ X) {m : G} :
    m ∈ centralizerSection M X Z ↔ m ∈ M ∧ ∀ x ∈ X, x * m * x⁻¹ * m⁻¹ ∈ Z := by
  refine ⟨fun h => ⟨h.1, h.2.2.2⟩, fun ⟨hM, h⟩ => ⟨hM, ?_, ?_, h⟩⟩
  · refine A4.mem_normalizer_of_conj_mem fun x hx => ?_
    have h1 := h x⁻¹ (X.inv_mem hx)
    have : m * x * m⁻¹ = x * (x⁻¹ * m * x⁻¹⁻¹ * m⁻¹) := by group
    rw [this]
    exact X.mul_mem hx (hZX h1)
  · refine A4.mem_normalizer_of_conj_mem fun z hz => ?_
    have h1 := h z⁻¹ (hZX (Z.inv_mem hz))
    have : m * z * m⁻¹ = z * (z⁻¹ * m * z⁻¹⁻¹ * m⁻¹) := by group
    rw [this]
    exact Z.mul_mem hz h1

theorem le_centralizerSection_iff [Finite G] {M X Z S : Subgroup G} (hZX : Z ≤ X) :
    S ≤ centralizerSection M X Z ↔ S ≤ M ∧ ⁅X, S⁆ ≤ Z := by
  constructor
  · intro h
    refine ⟨fun s hs => (h hs).1, (Subgroup.commutator_le).mpr fun x hx s hs => ?_⟩
    exact (h hs).2.2.2 x hx
  · rintro ⟨hSM, hc⟩ s hs
    rw [mem_centralizerSection_iff_of_le hZX]
    exact ⟨hSM hs, fun x hx => (Subgroup.commutator_le.mp hc) x hx s hs⟩

theorem conj_mem_centralizerSection {M X Z : Subgroup G} {g m : G}
    (hgM : g ∈ Subgroup.normalizer (M : Set G)) (hgX : g ∈ Subgroup.normalizer (X : Set G))
    (hgZ : g ∈ Subgroup.normalizer (Z : Set G)) (hm : m ∈ centralizerSection M X Z) :
    g * m * g⁻¹ ∈ centralizerSection M X Z := by
  obtain ⟨hmM, hmX, hmZ, hc⟩ := hm
  refine ⟨(Subgroup.mem_normalizer_iff.mp hgM m).mp hmM, ?_, ?_, fun x hx => ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgX hmX) (Subgroup.inv_mem _ hgX)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgZ hmZ) (Subgroup.inv_mem _ hgZ)
  · have hx' : g⁻¹ * x * g ∈ X := by
      have := (Subgroup.mem_normalizer_iff''.mp hgX x).mp hx
      exact this
    have h1 := (Subgroup.mem_normalizer_iff.mp hgZ _).mp (hc _ hx')
    have : x * (g * m * g⁻¹) * x⁻¹ * (g * m * g⁻¹)⁻¹ =
        g * ((g⁻¹ * x * g) * m * (g⁻¹ * x * g)⁻¹ * m⁻¹) * g⁻¹ := by group
    rw [this]
    exact h1

@[expose] def IsSignalizer (M X R : Subgroup G) : Prop :=
  R ≤ M ∧ IsPGroup 2 R ∧ X ≤ Subgroup.normalizer (R : Set G)

@[expose] def IsMaxSignalizer (M X R : Subgroup G) : Prop := Maximal (IsSignalizer M X) R

theorem IsMaxSignalizer.isSignalizer {M X R : Subgroup G} (h : IsMaxSignalizer M X R) :
    IsSignalizer M X R := h.1

theorem IsMaxSignalizer.eq_of_le {M X R S : Subgroup G} (h : IsMaxSignalizer M X R)
    (hS : IsSignalizer M X S) (hRS : R ≤ S) : S = R :=
  le_antisymm (h.2 hS hRS) hRS

theorem isMaxSignalizer_iff {M X R : Subgroup G} :
    IsMaxSignalizer M X R ↔
      IsSignalizer M X R ∧ ∀ S, IsSignalizer M X S → R ≤ S → S = R :=
  ⟨fun h => ⟨h.1, fun _ hS hRS => h.eq_of_le hS hRS⟩,
    fun ⟨h1, h2⟩ => ⟨h1, fun _ hS hRS => (h2 _ hS hRS).le⟩⟩

theorem exists_isMaxSignalizer_ge [Finite G] {M X P : Subgroup G} (hP : IsSignalizer M X P) :
    ∃ R, IsMaxSignalizer M X R ∧ P ≤ R := by
  obtain ⟨R, hPR, hR⟩ := Finite.exists_le_maximal hP
  exact ⟨R, hR, hPR⟩

theorem isSignalizer_iff_commutator_le {M X R : Subgroup G} (hRM : R ≤ M) (hR : IsPGroup 2 R) :
    IsSignalizer M X R ↔ ⁅X, R⁆ ≤ R := by
  constructor
  · rintro ⟨-, -, hX⟩
    refine Subgroup.commutator_le.mpr fun x hx r hr => ?_
    have := (Subgroup.mem_normalizer_iff.mp (hX hx) r).mp hr
    exact R.mul_mem this (R.inv_mem hr)
  · intro h
    refine ⟨hRM, hR, fun x hx => ?_⟩
    have hmem : ∀ x ∈ X, ∀ r ∈ R, x * r * x⁻¹ ∈ R := fun x hx r hr => by
      have h1 : x * r * x⁻¹ * r⁻¹ ∈ R := Subgroup.commutator_le.mp h x hx r hr
      have := R.mul_mem h1 hr
      simpa [mul_assoc] using this
    rw [Subgroup.mem_normalizer_iff]
    intro r
    refine ⟨hmem x hx r, fun hr => ?_⟩
    have := hmem x⁻¹ (X.inv_mem hx) _ hr
    simpa [mul_assoc] using this

@[expose] def IsXClass (Y : Subgroup G) : Prop := Y ≠ ⊥ ∧ Y = oTwoUpper Y ∧ CharTwo Y

@[expose] def VYR (Y R : Subgroup G) : Subgroup G := ⁅omegaOneCenterOf R, Y⁆

@[expose] def VY (Y : Subgroup G) : Subgroup G := VYR Y (pCoreOf 2 Y)

@[expose] def IsXf (Y : Subgroup G) : Prop := IsXClass Y ∧ VY Y ≠ ⊥

@[expose] def IsTwoChiefFactorOutsideO2 (X A B : Subgroup G) : Prop :=
  pCoreOf 2 X ≤ B ∧ B < A ∧ A ≤ X ∧ X ≤ Subgroup.normalizer (A : Set G) ∧
    X ≤ Subgroup.normalizer (B : Set G) ∧
    (∀ C : Subgroup G, B < C → C < A → ¬ X ≤ Subgroup.normalizer (C : Set G)) ∧
    ∀ a ∈ A, ∃ k : ℕ, a ^ 2 ^ k ∈ B

@[expose] def NoncentralTwoChiefFactorsInO2 (X : Subgroup G) : Prop :=
  ∀ A B : Subgroup G, IsTwoChiefFactorOutsideO2 X A B → ⁅A, X⁆ ≤ B

@[expose] def TwoChiefFactorsInO2 (X : Subgroup G) : Prop :=
  ∀ A B : Subgroup G, ¬ IsTwoChiefFactorOutsideO2 X A B

@[expose] def twoReducedJoin (M : Subgroup G) : Subgroup G :=
  ⨆ (V : Subgroup G) (_ : IsTwoReducedIn M V), V


namespace A4

theorem normalizerMonoidHom_eq_one_iff {V : Subgroup G} {g : Subgroup.normalizer (V : Set G)} :
    V.normalizerMonoidHom g = 1 ↔ (g : G) ∈ Subgroup.centralizer (V : Set G) := by
  rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]

theorem mem_normalizer_commutator {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer (⁅A, B⁆ : Subgroup G) := by
  have key : ∀ g : G, g ∈ Subgroup.normalizer (A : Set G) → g ∈ Subgroup.normalizer (B : Set G) →
      ∀ y ∈ ⁅A, B⁆, g * y * g⁻¹ ∈ ⁅A, B⁆ := by
    intro g hA hB y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      have h1 := (Subgroup.mem_normalizer_iff.mp hA a).mp ha
      have h2 := (Subgroup.mem_normalizer_iff.mp hB b).mp hb
      have h3 := Subgroup.commutator_mem_commutator h1 h2
      have : g * (a * b * a⁻¹ * b⁻¹) * g⁻¹ =
          (g * a * g⁻¹) * (g * b * g⁻¹) * (g * a * g⁻¹)⁻¹ * (g * b * g⁻¹)⁻¹ := by group
      show g * (a * b * a⁻¹ * b⁻¹) * g⁻¹ ∈ ⁅A, B⁆
      rw [this]
      exact h3
    | one => simp
    | mul x y _ _ ihx ihy => simpa [mul_assoc] using (⁅A, B⁆ : Subgroup G).mul_mem ihx ihy
    | inv x _ ih => simpa [mul_assoc] using (⁅A, B⁆ : Subgroup G).inv_mem ih
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g hA hB x hx, fun hx => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hA) (Subgroup.inv_mem _ hB) _ hx
  simpa [mul_assoc] using this

end A4

end CFSG.Quasithin
