module

public import CFSG.Quasithin.Vol2.Ch11SecE41Three

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

@[expose] def Out2Closed (X : Type*) [Group X] : Prop :=
  ∃ A : Subgroup (MulAut X), A.Normal ∧ (MulAut.conj : X →* MulAut X).range ≤ A ∧
    (∀ α ∈ A, ∃ k : ℕ, α ^ 2 ^ k ∈ (MulAut.conj : X →* MulAut X).range) ∧
    ∀ α : MulAut X, ∃ m : ℕ, Odd m ∧ α ^ m ∈ A

variable {G : Type} [Group G]

@[expose] noncomputable def quotAut (K : Subgroup G) :
    MulAut ↥K →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K) where
  toFun α := QuotientGroup.congr _ _ α
    (Subgroup.characteristic_iff_map_eq.mp inferInstance α)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' α β := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

@[expose] noncomputable def normAut (K : Subgroup G) :
    ↥(Subgroup.normalizer (K : Set G)) →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K) :=
  (quotAut K).comp (conjAct K)

theorem normAut_mk (K : Subgroup G) (g : ↥(Subgroup.normalizer (K : Set G))) (k : ↥K) :
    normAut K g (QuotientGroup.mk k) =
      QuotientGroup.mk ⟨(g : G) * k * (g : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp g.2 k).mp k.2⟩ := by
  apply congrArg QuotientGroup.mk
  apply Subtype.ext
  exact Subgroup.normalizerMonoidHom_apply_apply_coe K (Subgroup.inclusion le_rfl g) k

theorem mk_eq_one_iff (K : Subgroup G) (k : ↥K) :
    (QuotientGroup.mk k : ↥K ⧸ CFSG.pCore 2 ↥K) = 1 ↔ (k : G) ∈ pCoreOf 2 K := by
  rw [QuotientGroup.eq_one_iff, ← SecD.pCoreOf_subgroupOf, Subgroup.mem_subgroupOf]

theorem normAut_eq_one_iff [Finite G] (K : Subgroup G) (g : ↥(Subgroup.normalizer (K : Set G))) :
    normAut K g = 1 ↔ ∀ k ∈ K, (g : G) * k * (g : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmem : ∀ y : ↥K, y ∈ CFSG.pCore 2 ↥K ↔ (y : G) ∈ pCoreOf 2 K := fun y => by
    rw [← SecD.pCoreOf_subgroupOf, Subgroup.mem_subgroupOf]
  have hQn : ∀ y ∈ K, ∀ c ∈ pCoreOf 2 K, y * c * y⁻¹ ∈ pCoreOf 2 K := fun y hy c hc =>
    (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hy) c).mp hc
  have hgk : ∀ k ∈ K, (g : G) * k * (g : G)⁻¹ ∈ K := fun k hk =>
    (Subgroup.mem_normalizer_iff.mp g.2 k).mp hk
  constructor
  · intro h1 k hk
    have h2 : normAut K g (QuotientGroup.mk ⟨k, hk⟩) = QuotientGroup.mk ⟨k, hk⟩ := by
      rw [h1]
      rfl
    rw [normAut_mk, QuotientGroup.eq, hmem] at h2
    have h3 : ((g : G) * k * (g : G)⁻¹)⁻¹ * k ∈ pCoreOf 2 K := by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h2
    have h4 := hQn _ (hgk k hk) _ h3
    have e : (g : G) * k * (g : G)⁻¹ * (((g : G) * k * (g : G)⁻¹)⁻¹ * k) *
        ((g : G) * k * (g : G)⁻¹)⁻¹ = ((g : G) * k * (g : G)⁻¹ * k⁻¹)⁻¹ := by group
    rw [e] at h4
    simpa using (pCoreOf 2 K).inv_mem h4
  · intro h
    ext x
    induction x using QuotientGroup.induction_on with
    | H k =>
      rw [normAut_mk, MulAut.one_apply, QuotientGroup.eq, hmem]
      have h4 := hQn _ (K.inv_mem (hgk k k.2)) _ ((pCoreOf 2 K).inv_mem (h k k.2))
      have e : ((g : G) * k * (g : G)⁻¹)⁻¹ * ((g : G) * k * (g : G)⁻¹ * (k : G)⁻¹)⁻¹ *
          ((g : G) * k * (g : G)⁻¹)⁻¹⁻¹ = ((g : G) * k * (g : G)⁻¹)⁻¹ * k := by group
      rw [e] at h4
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h4

theorem normAut_of_mem (K : Subgroup G) (g : ↥(Subgroup.normalizer (K : Set G)))
    (hg : (g : G) ∈ K) :
    normAut K g = MulAut.conj (QuotientGroup.mk ⟨g, hg⟩ : ↥K ⧸ CFSG.pCore 2 ↥K) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H k =>
    rw [normAut_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1

variable [Finite G]

theorem exists_mul_of_sylow_of_two_quot {P Q S : Subgroup G} (hQP : Q ≤ P)
    (hQn : P ≤ Subgroup.normalizer (Q : Set G)) (hSP : QuasithinUnique.IsSylowTwoOf S P)
    (h2 : ∀ g ∈ P, ∃ k : ℕ, g ^ 2 ^ k ∈ Q) : ∀ g ∈ P, ∃ q ∈ Q, ∃ s ∈ S, g = q * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSQ : S ≤ Subgroup.normalizer (Q : Set G) := hSP.1.trans hQn
  have hHP : Q ⊔ S ≤ P := sup_le hQP hSP.1
  have : (Q.subgroupOf P).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).mpr hQn
  have hq : IsPGroup 2 (↥P ⧸ Q.subgroupOf P) := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H y =>
      obtain ⟨k, hk⟩ := h2 y y.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using hk
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp hq
  have hQidx : Q.relIndex P = 2 ^ a := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card, ha]
  have h1 := Subgroup.relIndex_mul_relIndex Q (Q ⊔ S) P le_sup_left hHP
  have h3 := Subgroup.relIndex_mul_relIndex S (Q ⊔ S) P le_sup_right hHP
  have hdvd2 : (Q ⊔ S).relIndex P ∣ 2 ^ a := hQidx ▸ Dvd.intro_left _ h1
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2
  have hodd : ¬ 2 ∣ (Q ⊔ S).relIndex P := fun hd =>
    hSP.2.2 (by
      change 2 ∣ S.relIndex P
      rw [← h3]
      exact hd.mul_left _)
  have hb0 : b = 0 := by
    by_contra hb0
    exact hodd (hb ▸ dvd_pow_self 2 hb0)
  rw [hb0, pow_zero] at hb
  have hPH : P ≤ Q ⊔ S := Subgroup.relIndex_eq_one.mp hb
  intro g hg
  have hg' : g ∈ ((Q ⊔ S : Subgroup G) : Set G) := hPH hg
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Q S hSQ] at hg'
  obtain ⟨q, hq, s, hs, rfl⟩ := hg'
  exact ⟨q, hq, s, hs, rfl⟩

theorem mem_of_pow_odd_mem {H : Type*} [Group H] {A : Subgroup H} {x : H} {m a : ℕ} (hm : Odd m)
    (hxm : x ^ m ∈ A) (hxa : x ^ 2 ^ a = 1) : x ∈ A := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [pow_zero, pow_one] at hxa
    rw [hxa]
    exact A.one_mem
  have hcop : Nat.Coprime m (2 ^ a) :=
    Nat.Coprime.pow_right a ((Nat.coprime_two_right).mpr hm)
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop
    (Nat.one_lt_two_pow (by omega))
  have e : x ^ (m * u) = x := by
    rw [← Nat.div_add_mod (m * u) (2 ^ a), hu, pow_add, pow_mul, hxa, one_pow, one_mul, pow_one]
  rw [← e, pow_mul]
  exact A.pow_mem hxm u

theorem exists_mul_of_frattini {N Ñ S : Subgroup G} (hÑN : Ñ ≤ N)
    (hNÑ : N ≤ Subgroup.normalizer (Ñ : Set G)) (hS : QuasithinUnique.IsSylowTwoOf S Ñ) :
    ∀ g ∈ N, ∃ x ∈ Ñ, ∃ m ∈ N ⊓ Subgroup.normalizer (S : Set G), g = x * m := by
  intro g hg
  have h := B6.frattini_two hÑN hNÑ hS hg
  rw [← SetLike.mem_coe,
    Subgroup.coe_mul_of_right_le_normalizer_left Ñ _ (inf_le_left.trans hNÑ)] at h
  obtain ⟨x, hx, m, hm, rfl⟩ := h
  exact ⟨x, hx, m, hm, rfl⟩

theorem exists_mul_of_out2Closed {N K T : Subgroup G} (hKN : K ≤ N)
    (hNK : N ≤ Subgroup.normalizer (K : Set G)) (hT : QuasithinUnique.IsSylowTwoOf T N)
    (hout : Out2Closed (↥K ⧸ CFSG.pCore 2 ↥K)) :
    ∀ g ∈ N, ∃ k ∈ K, ∃ y ∈ N ⊓ sectionCentralizer K (pCoreOf 2 K),
      ∃ m ∈ N ⊓ Subgroup.normalizer (T : Set G), g = k * y * m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hAn, hInn, hA2, hAodd⟩ := hout
  set φ := normAut K with hφ
  set Y := N ⊓ sectionCentralizer K (pCoreOf 2 K) with hY
  set Ñ : Subgroup G := N ⊓ (A.comap φ).map (Subgroup.normalizer (K : Set G)).subtype with hÑ
  have hNO : N ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    hNK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  have hmemÑ : ∀ g (hg : g ∈ N), g ∈ Ñ ↔ φ ⟨g, hNK hg⟩ ∈ A := by
    intro g hg
    constructor
    · rintro ⟨-, x, hx, rfl⟩
      exact hx
    · intro h
      exact ⟨hg, ⟨g, hNK hg⟩, h, rfl⟩
  have hφmul : ∀ (a b : G) (ha : a ∈ Subgroup.normalizer (K : Set G))
      (hb : b ∈ Subgroup.normalizer (K : Set G)),
      φ ⟨a * b, Subgroup.mul_mem _ ha hb⟩ = φ ⟨a, ha⟩ * φ ⟨b, hb⟩ := fun a b ha hb => by
    rw [← map_mul]
    rfl
  have hφinv : ∀ (a : G) (ha : a ∈ Subgroup.normalizer (K : Set G)),
      φ ⟨a⁻¹, Subgroup.inv_mem _ ha⟩ = (φ ⟨a, ha⟩)⁻¹ := fun a ha => by
    rw [← map_inv]
    rfl
  have hÑN : Ñ ≤ N := inf_le_left
  have hNÑ : N ≤ Subgroup.normalizer (Ñ : Set G) := by
    intro g hg
    apply A4.mem_normalizer_of_conj_mem
    intro x hx
    have hxN := hÑN hx
    have hgx : g * x * g⁻¹ ∈ N := N.mul_mem (N.mul_mem hg hxN) (N.inv_mem hg)
    rw [hmemÑ _ hgx]
    rw [hmemÑ _ hxN] at hx
    have e := hφmul (g * x) g⁻¹ (Subgroup.mul_mem _ (hNK hg) (hNK hxN))
      (Subgroup.inv_mem _ (hNK hg))
    rw [hφmul g x (hNK hg) (hNK hxN), hφinv g (hNK hg)] at e
    rw [e]
    exact hAn.conj_mem _ hx _
  have hKÑ : K ≤ Ñ := fun k hk => by
    rw [hmemÑ _ (hKN hk), normAut_of_mem K _ hk]
    exact hInn ⟨_, rfl⟩
  have hYÑ : Y ≤ Ñ := fun y hy => by
    rw [hmemÑ _ hy.1, (normAut_eq_one_iff K _).mpr fun k hk => hy.2.2.2 k hk]
    exact A.one_mem
  have hTÑ : T ≤ Ñ := fun t ht => by
    have htN := hT.1 ht
    rw [hmemÑ _ htN]
    obtain ⟨a, ha⟩ := exists_pow_two_pow_eq_one_of_mem hT.2.1 ht
    obtain ⟨m, hm, hmA⟩ := hAodd (φ ⟨t, hNK htN⟩)
    refine mem_of_pow_odd_mem hm hmA (a := a) ?_
    rw [← map_pow]
    have e : (⟨t, hNK htN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 2 ^ a = 1 :=
      Subtype.ext (by simpa using ha)
    rw [e, map_one]
  have h2 : ∀ g ∈ Ñ, ∃ k : ℕ, g ^ 2 ^ k ∈ K ⊔ Y := by
    intro g hg
    have hgN := hÑN hg
    obtain ⟨k, hk⟩ := hA2 _ ((hmemÑ _ hgN).mp hg)
    obtain ⟨xbar, hxbar⟩ := hk
    obtain ⟨k0, rfl⟩ := QuotientGroup.mk_surjective xbar
    refine ⟨k, ?_⟩
    have hk0N : (k0 : G) ∈ N := hKN k0.2
    have hgk : g ^ 2 ^ k * (k0 : G)⁻¹ ∈ N := N.mul_mem (N.pow_mem hgN _) (N.inv_mem hk0N)
    have hy : g ^ 2 ^ k * (k0 : G)⁻¹ ∈ Y := by
      refine ⟨hgk, hNK hgk, hNO hgk, ?_⟩
      refine (normAut_eq_one_iff K ⟨_, hNK hgk⟩).mp ?_
      have e1 := hφmul (g ^ 2 ^ k) (k0 : G)⁻¹ (Subgroup.pow_mem _ (hNK hgN) _)
        (Subgroup.inv_mem _ (hNK hk0N))
      rw [hφinv _ (hNK hk0N), normAut_of_mem K ⟨(k0 : G), hNK hk0N⟩ k0.2] at e1
      have e2 : φ ⟨g ^ 2 ^ k, Subgroup.pow_mem _ (hNK hgN) _⟩ = (φ ⟨g, hNK hgN⟩) ^ 2 ^ k := by
        rw [← map_pow]
        rfl
      rw [e2, ← hxbar] at e1
      rw [e1]
      simp
    have e : g ^ 2 ^ k = g ^ 2 ^ k * (k0 : G)⁻¹ * k0 := by group
    rw [e]
    exact (K ⊔ Y).mul_mem (Subgroup.mem_sup_right hy) (Subgroup.mem_sup_left k0.2)
  have hYn : N ≤ Subgroup.normalizer (Y : Set G) := fun g hg =>
    SecD.mem_normalizer_inf (Subgroup.le_normalizer hg)
      (SecD.mem_normalizer_sectionCentralizer (hNK hg) (hNO hg))
  have hQn : N ≤ Subgroup.normalizer ((K ⊔ Y : Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_sup_of (hNK hg) (hYn hg)
  have hTsyl : QuasithinUnique.IsSylowTwoOf T Ñ := by
    refine ⟨hTÑ, hT.2.1, fun hd => hT.2.2 ?_⟩
    have h1 := Subgroup.relIndex_mul_relIndex T Ñ N hTÑ hÑN
    change 2 ∣ T.relIndex N
    rw [← h1]
    exact hd.mul_right _
  have hQT := exists_mul_of_sylow_of_two_quot (sup_le hKÑ hYÑ) (hÑN.trans hQn) hTsyl h2
  intro g hg
  obtain ⟨x, hx, m, hm, rfl⟩ := exists_mul_of_frattini hÑN hNÑ hTsyl g hg
  obtain ⟨q, hq, t, ht, rfl⟩ := hQT x hx
  have hq' : q ∈ ((K ⊔ Y : Subgroup G) : Set G) := hq
  rw [Subgroup.coe_mul_of_right_le_normalizer_left K Y (inf_le_left.trans hNK)] at hq'
  obtain ⟨k, hk, y, hy, rfl⟩ := hq'
  refine ⟨k, hk, y, hy, t * m, ⟨N.mul_mem (hT.1 ht) hm.1,
    Subgroup.mul_mem _ (Subgroup.le_normalizer ht) hm.2⟩, ?_⟩
  group

end CFSG.Quasithin.Vol2.Ch11.SecE
