module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15420Avg
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15420Comp

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace L15420

variable {G : Type*} [Group G]

@[expose] noncomputable def quotConjHom (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) →* MulAut (↥L ⧸ CFSG.pCore 2 ↥L) where
  toFun g := quotConj L g g.2
  map_one' := quotConj_one
  map_mul' g h := quotConj_mul g.2 h.2

@[expose] noncomputable def quotCent (L : Subgroup G) : Subgroup G :=
  (quotConjHom L).ker.map (Subgroup.normalizer (L : Set G)).subtype

theorem mem_quotCent {L : Subgroup G} {g : G} :
    g ∈ quotCent L ↔ ∃ hg : g ∈ Subgroup.normalizer (L : Set G), quotConj L g hg = 1 := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h.2, hh⟩
  · rintro ⟨hg, h1⟩
    exact ⟨⟨g, hg⟩, h1, rfl⟩

theorem normalizer_le_normalizer_quotCent (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (quotCent L : Set G) := by
  have key : ∀ h ∈ Subgroup.normalizer (L : Set G), ∀ g ∈ quotCent L, h * g * h⁻¹ ∈ quotCent L := by
    intro h hh g hg
    obtain ⟨hgN, hg1⟩ := mem_quotCent.mp hg
    refine mem_quotCent.mpr ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hh hgN) (Subgroup.inv_mem _ hh),
      ?_⟩
    have hinv : quotConj L h⁻¹ (Subgroup.inv_mem _ hh) * quotConj L h hh = 1 := by
      rw [← quotConj_mul, quotConj_congr (inv_mul_cancel h) _ (Subgroup.one_mem _), quotConj_one]
    rw [quotConj_mul (Subgroup.mul_mem _ hh hgN) (Subgroup.inv_mem _ hh), quotConj_mul hh hgN, hg1,
      mul_one]
    calc quotConj L h hh * quotConj L h⁻¹ (Subgroup.inv_mem _ hh)
        = quotConj L h hh * quotConj L h⁻¹ (Subgroup.inv_mem _ hh) * 1 := by rw [mul_one]
      _ = 1 := by
        rw [← quotConj_mul, quotConj_congr (mul_inv_cancel h) _ (Subgroup.one_mem _),
          quotConj_one, one_mul]
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨key h hh g, fun hg => ?_⟩
  have := key h⁻¹ (Subgroup.inv_mem _ hh) _ hg
  simpa [mul_assoc] using this

end L15420

variable {G : Type} [Group G] [Finite G] {T : Subgroup G}

namespace Config15420

variable {s : Setting15419 G T} {I₀ : Subgroup G}

theorem R_le_TI (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T)
    (c : Config15420 s I₀) : pCoreOf 2 (s.X ⊔ T ⊓ I₀) ≤ T ⊓ I₀ :=
  L15420.pCoreOf_le_of_isSylowTwoOf
    (L15420.isSylowTwoOf_of_le_of_le c.sylow le_sup_right (sup_le (c.le_X hyp h12) inf_le_right))

theorem R_ne_bot (hyp : MultipleCentralizerHypothesis G T) (c : Config15420 s I₀) :
    pCoreOf 2 (s.X ⊔ T ⊓ I₀) ≠ ⊥ := by
  have hT : T ≠ ⊥ := by
    obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo hyp.sylow
    have := hyp.simple
    rw [← hS]
    exact sylow_ne_bot hyp.nonabelian S
  have hZ : quasithinOmegaOneCenter T ≠ ⊥ :=
    CFSG.Quasithin.quasithinOmegaOneCenter_ne_bot hyp.sylow.1 hT
  exact fun h => hZ (le_bot_iff.mp (h ▸ c.omegaOneCenter_le_R hyp))

theorem inf_le_R (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T)
    (c : Config15420 s I₀) : T ⊓ I₀ ⊓ L15420.quotCent s.X ≤ pCoreOf 2 (s.X ⊔ T ⊓ I₀) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := T ⊓ I₀ ⊓ L15420.quotCent s.X with hDdef
  have hTX : T ⊓ I₀ ≤ Subgroup.normalizer (s.X : Set G) :=
    (inf_le_left.trans s.inM₁.2).trans (M₁_le_normalizer_X h12 s)
  have hQD : pCoreOf 2 s.X ≤ D := by
    intro q hq
    have hqX : q ∈ s.X := CFSG.LieType.BorelTits.pCoreOf_le 2 s.X hq
    refine ⟨c.pCoreOf_X_le_TI hyp h12 hq, L15420.mem_quotCent.mpr ⟨Subgroup.le_normalizer hqX, ?_⟩⟩
    rw [L15420.quotConj_eq_one_iff]
    intro x hx
    have h1 : x * q⁻¹ * x⁻¹ ∈ pCoreOf 2 s.X :=
      (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 s.X hx)
        _).mp ((pCoreOf 2 s.X).inv_mem hq)
    have e : q * x * q⁻¹ * x⁻¹ = q * (x * q⁻¹ * x⁻¹) := by group
    rw [e]
    exact (pCoreOf 2 s.X).mul_mem hq h1
  have hXD : ∀ x ∈ s.X, ∀ d ∈ D, x * d * x⁻¹ ∈ D := by
    intro x hx d hd
    obtain ⟨hdN, hd1⟩ := L15420.mem_quotCent.mp hd.2
    have h1 := (L15420.quotConj_eq_one_iff hdN).mp hd1 x hx
    have h2 : x * d * x⁻¹ * d⁻¹ ∈ pCoreOf 2 s.X := by
      have := (pCoreOf 2 s.X).inv_mem h1
      simpa [mul_assoc] using this
    have e : x * d * x⁻¹ = (x * d * x⁻¹ * d⁻¹) * d := by group
    rw [e]
    exact D.mul_mem (hQD h2) hd
  have hND : s.X ⊔ T ⊓ I₀ ≤ Subgroup.normalizer (D : Set G) := by
    refine sup_le (fun x hx => ?_) (fun t ht => ?_)
    · rw [Subgroup.mem_normalizer_iff]
      intro d
      refine ⟨hXD x hx d, fun h => ?_⟩
      have := hXD x⁻¹ (s.X.inv_mem hx) _ h
      simpa [mul_assoc] using this
    · exact L15420.mem_normalizer_inf (Subgroup.le_normalizer ht)
        (L15420.normalizer_le_normalizer_quotCent s.X (hTX ht))
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_right) hND
    ((hyp.sylow.1.to_le (inf_le_left.trans inf_le_left)))

theorem hypC23 (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T)
    (c : Config15420 s I₀) : HypC23Cat I₀ (pCoreOf 2 (s.X ⊔ T ⊓ I₀)) (I₀ ⊓ s.M₁) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 (s.X ⊔ T ⊓ I₀) with hRdef
  have hXI : s.X ⊔ T ⊓ I₀ ≤ I₀ := sup_le (c.le_X hyp h12) inf_le_right
  have hRTI : R ≤ T ⊓ I₀ := c.R_le_TI hyp h12
  have hRI : R ≤ I₀ := hRTI.trans inf_le_right
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hTR : T ≤ Subgroup.normalizer (R : Set G) := c.le_normalizer_R hyp h12
  have hTX : T ≤ Subgroup.normalizer (s.X : Set G) := s.inM₁.2.trans (M₁_le_normalizer_X h12 s)
  refine ⟨isSQTKCat_of_hyp hyp c.inH.2, ⟨hRI, c.R_ne_bot hyp, ?_⟩, inf_le_left, ?_, ?_⟩
  ·
    set N := I₀ ⊓ Subgroup.normalizer (R : Set G) with hNdef
    refine le_antisymm (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (le_inf hRI Subgroup.le_normalizer) inf_le_right hR2) ?_
    have hTIN : T ⊓ I₀ ≤ N := le_inf inf_le_right (inf_le_left.trans hTR)
    have hsyl : IsSylowTwoOf (T ⊓ I₀) N := L15420.isSylowTwoOf_of_le_of_le c.sylow hTIN inf_le_left
    have hQT : pCoreOf 2 N ≤ T ⊓ I₀ := L15420.pCoreOf_le_of_isSylowTwoOf hsyl
    have hXN : s.X ⊔ T ⊓ I₀ ≤ N :=
      le_inf hXI (sup_le Config15420.X_le_normalizer_R (inf_le_left.trans hTR))
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hQT.trans le_sup_right)
      (hXN.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)
  ·
    exact iSup_le fun C => iSup_le fun hCR => iSup_le fun hC => iSup_le fun hchar =>
      le_inf inf_le_left (inf_le_right.trans (c.normalizer_le_M₁ hyp h12 hCR hC hchar))
  ·
    set M := I₀ ⊓ s.M₁ with hMdef
    set N := conjClosure R M with hNdef
    have hTIM : T ⊓ I₀ ≤ M := le_inf inf_le_right (inf_le_left.trans s.inM₁.2)
    have hsylM : IsSylowTwoOf (T ⊓ I₀) M := L15420.isSylowTwoOf_of_le_of_le c.sylow hTIM inf_le_left
    have hRM : R ≤ M := hRTI.trans hTIM
    have hNM : N ≤ M := conjClosure_le fun h hh r hr =>
      M.mul_mem (M.mul_mem hh (hRM hr)) (M.inv_mem hh)
    have hMN : M ≤ Subgroup.normalizer (N : Set G) := le_normalizer_conjClosure R M
    have h1 := A4.isSylowTwoOf_inf_normal hsylM hNM hMN
    have hMX : M ≤ Subgroup.normalizer (s.X : Set G) :=
      inf_le_right.trans (M₁_le_normalizer_X h12 s)
    have hRC : R ≤ L15420.quotCent s.X := by
      intro r hr
      refine L15420.mem_quotCent.mpr ⟨hMX (hRM hr), ?_⟩
      rw [L15420.quotConj_eq_one_iff]
      intro x hx
      have h := c.commutator_X_R_le hyp h12 (Subgroup.commutator_mem_commutator hx hr)
      have h' := (pCoreOf 2 s.X).inv_mem h
      simpa [commutatorElement_def, mul_assoc] using h'
    have hNC : N ≤ L15420.quotCent s.X := conjClosure_le fun h hh r hr =>
      (Subgroup.mem_normalizer_iff.mp (L15420.normalizer_le_normalizer_quotCent s.X (hMX hh))
        r).mp (hRC hr)
    have heq : T ⊓ I₀ ⊓ N = R := by
      refine le_antisymm ?_ (le_inf hRTI (le_conjClosure R M))
      exact (inf_le_inf_left _ hNC).trans (c.inf_le_R hyp h12)
    rw [heq] at h1
    exact h1

end Config15420

namespace Comp15420

variable {s : Setting15419 G T} {I₀ K : Subgroup G} {y : G}

theorem R_le_normalizer (facts : Facts15420) (hyp : MultipleCentralizerHypothesis G T)
    (h12 : Stmt15412 G T) (c : Config15420 s I₀) (hC : Comp15420 s I₀ K y) :
    pCoreOf 2 (s.X ⊔ T ⊓ I₀) ≤ Subgroup.normalizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro r hr
  have hrI : r ∈ I₀ := ((c.R_le_TI hyp h12).trans inf_le_right) hr
  refine L15420.mem_normalizer_of_conj_mem hC.mem hC.quasisimple (hC.center_eq_bot facts)
    hC.y_mem.2 hC.y_order hrI (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 s.X)
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 s.X).trans hC.X_le_normalizer) (ε := 1) (Or.inl rfl) ?_
  have h := c.commutator_X_R_le hyp h12 (Subgroup.commutator_mem_commutator hC.y_mem.1 hr)
  have h' := (pCoreOf 2 s.X).inv_mem h
  simpa [commutatorElement_def, mul_assoc] using h'

theorem not_le_M₁ (h2 : Stmt1542Two G T) (hC : Comp15420 s I₀ K y) : ¬ K ≤ s.M₁ := by
  intro hKM
  have hsolv : Group.IsSolvable s.M₁ := h2 s.M₁ s.inM₁
  have hKs : Group.IsSolvable K :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKM)
      (Subgroup.inclusion_injective hKM)
  have h := (isSolvable_iff_perfectCore_eq_bot K).mp hKs
  rw [perfectCore_eq_self_of_perfect (perfect_of_mem_cComp hC.mem)] at h
  exact ne_bot_of_mem_cComp hC.mem h

theorem isSylowTwoOf_sup (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T)
    (c : Config15420 s I₀) (hC : Comp15420 s I₀ K y)
    (hRK : pCoreOf 2 (s.X ⊔ T ⊓ I₀) ≤ Subgroup.normalizer (K : Set G)) :
    IsSylowTwoOf (T ⊓ I₀ ⊓ K ⊔ pCoreOf 2 (s.X ⊔ T ⊓ I₀)) (K ⊔ pCoreOf 2 (s.X ⊔ T ⊓ I₀)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 (s.X ⊔ T ⊓ I₀) with hRdef
  set TK := T ⊓ I₀ ⊓ K with hTKdef
  have hTK : IsSylowTwoOf TK K :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hC.mem) c.sylow
  have hRTI : R ≤ T ⊓ I₀ := c.R_le_TI hyp h12
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hRN : R ≤ Subgroup.normalizer (TK : Set G) := fun r hr =>
    L15420.mem_normalizer_inf (Subgroup.le_normalizer (hRTI hr)) (hRK hr)
  have hS2 : IsPGroup 2 ↥(TK ⊔ R) := IsPGroup.to_sup_of_normal_left' hTK.2.1 hR2 hRN
  have hSN : TK ⊔ R ≤ Subgroup.normalizer (K : Set G) :=
    sup_le (hTK.1.trans Subgroup.le_normalizer) hRK
  have hrel := L15420.relIndex_inf_eq hSN
  have hinf : (TK ⊔ R) ⊓ K = TK := inf_eq_of_isSylowTwoOf_of_le hTK hS2 le_sup_left
  have hsup : TK ⊔ R ⊔ K = K ⊔ R :=
    le_antisymm (sup_le (sup_le (hTK.1.trans le_sup_left) le_sup_right) le_sup_left)
      (sup_le le_sup_right (le_sup_right.trans le_sup_left))
  rw [hinf, hsup] at hrel
  refine ⟨sup_le (hTK.1.trans le_sup_left) le_sup_right, hS2, ?_⟩
  have h := hTK.2.2
  change ¬ 2 ∣ TK.relIndex K at h
  change ¬ 2 ∣ (TK ⊔ R).relIndex (K ⊔ R)
  rwa [hrel] at h

theorem pCoreOf_le_T (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T)
    (c : Config15420 s I₀) (hC : Comp15420 s I₀ K y)
    (hRK : pCoreOf 2 (s.X ⊔ T ⊓ I₀) ≤ Subgroup.normalizer (K : Set G)) :
    pCoreOf 2 (K ⊔ pCoreOf 2 (s.X ⊔ T ⊓ I₀)) ≤ T :=
  (L15420.pCoreOf_le_of_isSylowTwoOf (hC.isSylowTwoOf_sup hyp h12 c hRK)).trans
    (sup_le (inf_le_left.trans inf_le_left) ((c.R_le_TI hyp h12).trans inf_le_left))

theorem pCoreOf_le_pCoreOf_sup {R : Subgroup G} (hRK : R ≤ Subgroup.normalizer (K : Set G)) :
    pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ R) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans le_sup_left)
    (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
      (hRK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)

theorem false_of_fix (h8 : Stmt1548 G T) (hyp : MultipleCentralizerHypothesis G T)
    (c : Config15420 s I₀) (hC : Comp15420 s I₀ K y) {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hKV : K ≤ Subgroup.normalizer (V : Set G)) (hZV : quasithinOmegaOneCenter T ≤ V)
    {k₀ : G} (hk₀K : k₀ ∈ K) (hk₀ : ∀ n : ℕ, k₀ ^ 2 ^ n ≠ 1)
    (hfix : ∀ w ∈ ⁅V, K⁆, (∀ t ∈ T ⊓ I₀ ⊓ K, t * w = w * t) →
      k₀ * w * k₀⁻¹ * w⁻¹ ∈ Subgroup.centralizer (K : Set G)) : False := by
  set U := ⁅V, K⁆ with hUdef
  have hTK : IsSylowTwoOf (T ⊓ I₀ ⊓ K) K :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hC.mem) c.sylow
  have hUV : U ≤ V := commutator_le_of_le_normalizer hKV
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hV.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hV2 : ∀ v ∈ V, v * v = 1 := fun v hv => by rw [← sq]; exact hV.2 v hv
  have hKU : K ≤ Subgroup.normalizer (U : Set G) := fun k hk =>
    A4.mem_normalizer_commutator (hKV hk) (Subgroup.le_normalizer hk)
  obtain ⟨a, m, hm, hN⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos k₀).ne'
  set k := k₀ ^ 2 ^ a with hkdef
  have hkK : k ∈ K := K.pow_mem hk₀K _
  have hkZ : ∀ z ∈ quasithinOmegaOneCenter T, z * k = k * z := by
    intro z hz
    have hzT := L15420.omegaOneCenter_le_center T hz
    have hzTK : ∀ t ∈ T ⊓ I₀ ⊓ K, t * z = z * t := fun t ht =>
      Subgroup.mem_centralizer_iff.mp hzT.2 t ht.1.1
    have hδ : ∀ k' ∈ K, k' * z * k'⁻¹ * z⁻¹ ∈ U := by
      intro k' hk'
      have h := Subgroup.commutator_mem_commutator hk' (hZV hz)
      rw [Subgroup.commutator_comm] at h
      simpa [commutatorElement_def] using h
    obtain ⟨w, hwU, hw⟩ := L15420.exists_mul_mem_centralizer hTK.2.2
      (fun a ha b hb => hVc a (hUV ha) b (hUV hb)) (fun u hu => hV2 u (hUV hu)) hKU hzTK hδ
    have hwT : ∀ t ∈ T ⊓ I₀ ⊓ K, t * w = w * t := by
      intro t ht
      have h1 := hw t ht.2
      have h2 := hzTK t ht
      have e : w = z * (w⁻¹ * z)⁻¹ := by group
      rw [e]
      calc t * (z * (w⁻¹ * z)⁻¹) = (t * z) * (w⁻¹ * z)⁻¹ := by group
        _ = z * (t * (w⁻¹ * z)⁻¹) := by rw [h2]; group
        _ = z * ((w⁻¹ * z)⁻¹ * t) := by
          congr 1
          calc t * (w⁻¹ * z)⁻¹ = (w⁻¹ * z)⁻¹ * ((w⁻¹ * z) * t) * (w⁻¹ * z)⁻¹ := by group
            _ = (w⁻¹ * z)⁻¹ * (t * (w⁻¹ * z)) * (w⁻¹ * z)⁻¹ := by rw [h1]
            _ = (w⁻¹ * z)⁻¹ * t := by group
        _ = z * (w⁻¹ * z)⁻¹ * t := by group
    set cc := k₀ * w * k₀⁻¹ * w⁻¹ with hccdef
    have hccC := hfix w hwU hwT
    have hwV : w ∈ V := hUV hwU
    have hccV : cc ∈ V := V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKV hk₀K) w).mp hwV)
      (V.inv_mem hwV)
    have hkw : k * w = w * k := by
      refine L15420.pow_mul_comm_of_conj_eq (c := cc) (by rw [hccdef]; group) ?_
        (hV2 cc hccV) hm hN
      exact (Subgroup.mem_centralizer_iff.mp hccC k₀ hk₀K).symm
    have hkc := hw k hkK
    calc z * k = (w * (w⁻¹ * z)) * k := by group
      _ = w * ((w⁻¹ * z) * k) := by group
      _ = w * (k * (w⁻¹ * z)) := by rw [hkc]
      _ = (k * w) * (w⁻¹ * z) := by rw [hkw]; group
      _ = k * z := by group
  have hkT : k ∈ T :=
    (inf_centralizer_omegaOneCenter_le h8 I₀ ⟨le_of_mem_cComp hC.mem hkK,
      Subgroup.mem_centralizer_iff.mpr hkZ⟩).1
  obtain ⟨b, hb⟩ := hyp.sylow.1 ⟨k, hkT⟩
  have hkb : k ^ 2 ^ b = 1 := by
    have := congrArg Subtype.val hb
    simpa using this
  apply hk₀ (a + b)
  rw [pow_add, pow_mul]
  exact hkb

end Comp15420

end CFSG.Quasithin.EmptyFaithfulMultiple
