module

public import CFSG.LocalAnalysis.StandardType.GGSixOddIndexF4FactsTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBF4EndNode
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviRootSL2B2
public import CFSG.LieType.Chevalley.ToralCentralizerQuotient
public import CFSG.LieType.Ree.ReeTorus
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType

namespace F4Rest

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.SeitzReduction.F4Pilot CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Arith

theorem coeff03_check : ∀ γ ∈ rootFinset .F4, (γ 0 = 0 ∧ γ 3 = 0) ∨
    2 * γ 0 ^ 2 - γ 3 ^ 2 ∈ ({1, -1, 2, -2, 4, -4} : Finset ℤ) := by
  decide +kernel

theorem not_dvd_of_mem_small {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : ℤ}
    (hx : x ∈ ({1, -1, 2, -2, 4, -4} : Finset ℤ)) : ¬ (p : ℤ) ∣ x := by
  intro hd
  have h3 : 3 ≤ p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  have hpabs : (p : ℤ) ≤ |x| := Int.le_of_dvd (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    <;> norm_num) ((dvd_abs _ _).2 hd)
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num at hpabs; omega
  · norm_num at hpabs; omega
  · norm_num at hpabs; omega
  · norm_num at hpabs; omega
  · norm_num at hpabs
    have h4 : p = 3 ∨ p = 4 := by omega
    rcases h4 with rfl | rfl
    · norm_num at hd
    · exact absurd hp (by norm_num)
  · norm_num at hpabs
    have h4 : p = 3 ∨ p = 4 := by omega
    rcases h4 with rfl | rfl
    · norm_num at hd
    · exact absurd hp (by norm_num)

theorem eq_zero_of_zpow_eq_one {G : Type*} [Group G] {w : G} {p θ : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hw : orderOf w = p) (hθ : w ^ (2 * θ * θ) = w) {x y : ℤ}
    (hxy : (x = 0 ∧ y = 0) ∨ 2 * x ^ 2 - y ^ 2 ∈ ({1, -1, 2, -2, 4, -4} : Finset ℤ))
    (h1 : w ^ (x + (θ : ℤ) * y) = 1) : x = 0 ∧ y = 0 := by
  rcases hxy with h | hmem
  · exact h
  exfalso
  have hd1 : (p : ℤ) ∣ x + (θ : ℤ) * y := by
    rw [← hw]
    exact orderOf_dvd_iff_zpow_eq_one.2 h1
  have hd2 : (p : ℤ) ∣ 2 * (θ : ℤ) * θ - 1 := by
    rw [← hw]
    refine orderOf_dvd_iff_zpow_eq_one.2 ?_
    rw [zpow_sub, zpow_one, mul_inv_eq_one]
    exact_mod_cast hθ
  refine not_dvd_of_mem_small hp hp2 hmem ?_
  have e : 2 * x ^ 2 - y ^ 2 =
      2 * (x - θ * y) * (x + θ * y) + y ^ 2 * (2 * θ * θ - 1) := by ring
  rw [e]
  exact dvd_add (dvd_mul_of_dvd_right hd1 _) (dvd_mul_of_dvd_right hd2 _)

end Arith

section Element

variable {K : Type} [Field K]

@[expose] def b2Diag (w u : Kˣ) : Fin Tag.F4.rank → Kˣ := fun j =>
  w ^ (if j = 0 then (1 : ℤ) else 0) * u ^ (if j = 3 then (1 : ℤ) else 0)

theorem rootChar_b2Diag (w u : Kˣ) (γ : Fin Tag.F4.rank → ℤ) :
    rootChar (b2Diag w u) γ = w ^ γ 0 * u ^ γ 3 := by
  simp only [rootChar, b2Diag, mul_zpow, ← zpow_mul, Finset.prod_mul_distrib,
    Finset.prod_zpow_eq_zpow_sum, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

theorem wu_mul {G : Type*} [CommGroup G] (w u : G) (a₁ b₁ a₂ b₂ : ℤ) :
    w ^ a₁ * u ^ b₁ * (w ^ a₂ * u ^ b₂) = w ^ (a₁ + a₂) * u ^ (b₁ + b₂) := by
  rw [mul_mul_mul_comm, ← zpow_add, ← zpow_add]

theorem wu_zpow {G : Type*} [CommGroup G] (w u : G) (a b n : ℤ) :
    (w ^ a * u ^ b) ^ n = w ^ (a * n) * u ^ (b * n) := by
  rw [mul_zpow, ← zpow_mul, ← zpow_mul]

theorem cartan_exps : ∀ j : Fin Tag.F4.rank,
    (2 * Tag.F4.cartan 0 j + 1 * Tag.F4.cartan 3 j +
        (3 * Tag.F4.cartan 1 j + 2 * Tag.F4.cartan 2 j) = if j = 0 then 1 else 0) ∧
    (2 * Tag.F4.cartan 0 j + 2 * Tag.F4.cartan 3 j +
        (4 * Tag.F4.cartan 1 j + 3 * Tag.F4.cartan 2 j) = if j = 3 then 1 else 0) := by
  decide +kernel

theorem torusElt_prod_eq_b2Diag
    (w u : Kˣ) :
    torusElt .F4 K 0 (w ^ (2 : ℤ) * u ^ (2 : ℤ)) * torusElt .F4 K 3 (w ^ (1 : ℤ) * u ^ (2 : ℤ)) *
      (torusElt .F4 K 1 (w ^ (3 : ℤ) * u ^ (4 : ℤ)) *
        torusElt .F4 K 2 (w ^ (2 : ℤ) * u ^ (3 : ℤ))) = rootDiagUnit .F4 (b2Diag w u) := by
  rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit,
    torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul, ← rootDiagUnit_mul, ← rootDiagUnit_mul]
  congr 1
  funext j
  simp only [Pi.mul_apply, wu_zpow, wu_mul, b2Diag]
  rw [(cartan_exps j).1, (cartan_exps j).2]

theorem wu_pow_theta {G : Type*} [CommGroup G] {w : G} {θ : ℕ} (hθ : w ^ (2 * θ * θ) = w)
    (a c : ℤ) : (w ^ a * (w ^ θ) ^ (2 * c)) ^ θ = w ^ c * (w ^ θ) ^ a := by
  have hz : w ^ (2 * (θ : ℤ) * θ) = w := by
    rw [show 2 * (θ : ℤ) * θ = ((2 * θ * θ : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    exact hθ
  calc (w ^ a * (w ^ θ) ^ (2 * c)) ^ θ = w ^ ((a + θ * (2 * c)) * θ) := by
        rw [← zpow_natCast w θ, ← zpow_natCast _ θ, ← zpow_mul, ← zpow_add, ← zpow_mul]
    _ = (w ^ (2 * (θ : ℤ) * θ)) ^ c * w ^ ((θ : ℤ) * a) := by
        rw [← zpow_mul, ← zpow_add]
        congr 1
        ring
    _ = w ^ c * (w ^ θ) ^ a := by rw [hz, zpow_mul, zpow_natCast]

variable (K) in
@[expose] noncomputable def b2TorusElt
    (m : ℕ) (w : Kˣ) : adjointGroup .F4 K :=
  ReeTag.F4.reeTorus m 0 (w ^ (2 : ℤ) * (w ^ (2 ^ m)) ^ (2 : ℤ)) *
    ReeTag.F4.reeTorus m 1 (w ^ (3 : ℤ) * (w ^ (2 ^ m)) ^ (4 : ℤ))

theorem b2TorusElt_mem_reeFixed
    [Finite K] [CharP K ReeTag.F4.prime] {m : ℕ}
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (w : Kˣ) : b2TorusElt K m w ∈ reeFixed ReeTag.F4 K m :=
  mul_mem (ReeTag.F4.reeTorus_mem_reeFixed m hK (by decide) _)
    (ReeTag.F4.reeTorus_mem_reeFixed m hK (by decide) _)

theorem coe_b2TorusElt {m : ℕ}
    {w : Kˣ} (hw : w ^ (2 * 2 ^ m * 2 ^ m) = w) :
    (b2TorusElt K m w : ModGL .F4 K) =
      rootDiagUnit .F4 (b2Diag w (w ^ (2 ^ m))) := by
  have h0 := wu_pow_theta hw 2 1
  have h1 := wu_pow_theta hw 3 2
  simp only [mul_one, show (2 : ℤ) * 2 = 4 from rfl] at h0 h1
  rw [← torusElt_prod_eq_b2Diag]
  change torusElt .F4 K 0 _ * torusElt .F4 K (ReeTag.F4.perm 0) (_ ^ (2 ^ m)) *
    (torusElt .F4 K 1 _ * torusElt .F4 K (ReeTag.F4.perm 1) (_ ^ (2 ^ m))) = _
  rw [h0, h1]
  rfl

end Element

section Kernel

variable {K : Type} [Field K]

theorem rootCharKernel_b2Diag {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {w : Kˣ}
    (hw : orderOf w = p) (hθ : w ^ (2 * 2 ^ m * 2 ^ m) = w) :
    rootCharKernel (b2Diag w (w ^ (2 ^ m))) = b2LeviRoots := by
  ext γ
  change (IsRoot .F4 γ ∧ rootChar (b2Diag w (w ^ (2 ^ m))) γ = 1) ↔ γ ∈ b2LeviRoots
  rw [mem_b2LeviRoots, rootChar_b2Diag]
  refine and_congr_right fun hγ => ⟨fun h => ?_, fun h => by rw [h.1, h.2]; simp⟩
  have h' : w ^ (γ 0 + ((2 ^ m : ℕ) : ℤ) * γ 3) = 1 := by
    rw [zpow_add, zpow_mul, zpow_natCast]
    exact h
  exact eq_zero_of_zpow_eq_one hp hp2 hw hθ (coeff03_check γ (mem_rootFinset.2 hγ)) h'

end Kernel

section Component

theorem normal_subgroupOf_subgroupOf {G : Type*} [Group G] {A B C : Subgroup G} (hAB : A ≤ B)
    (h : (A.subgroupOf B).Normal) : ((A.subgroupOf C).subgroupOf (B.subgroupOf C)).Normal := by
  have hle : A.subgroupOf C ≤ B.subgroupOf C := fun x hx =>
    Subgroup.mem_subgroupOf.2 (hAB (Subgroup.mem_subgroupOf.1 hx))
  rw [Subgroup.normal_subgroupOf_iff hle]
  intro x y hx hy
  rw [Subgroup.mem_subgroupOf] at hx hy ⊢
  simpa using (Subgroup.normal_subgroupOf_iff hAB).1 h (x : G) (y : G) hx hy

theorem isQuasisimple_of_isSimpleGroup {Q : Type*} [Group Q] (hQ : IsSimpleGroup Q)
    (hZ : Subgroup.center Q = ⊥) : CFSG.Assembly.IsQuasisimple Q := by
  refine ⟨?_, ?_⟩
  · rcases hQ.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
    · exfalso
      have hc : (⊤ : Subgroup Q) ≤ Subgroup.centralizer (⊤ : Subgroup Q) := by
        rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, ← commutator_def]
        exact h
      have htop : Subgroup.center Q = ⊤ := by
        rw [eq_top_iff]
        intro g _
        rw [Subgroup.mem_center_iff]
        intro h'
        exact (Subgroup.mem_centralizer_iff.1 (hc (Subgroup.mem_top g)) h' (Subgroup.mem_top h'))
      rw [hZ] at htop
      exact bot_ne_top htop
    · exact h
  · exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup

variable {K : Type} [Field K]

theorem centralizer_eq_toralCentralizer
    {a : Fin Tag.F4.rank → Kˣ} {b : adjointGroup .F4 K}
    (hb : (b : ModGL .F4 K) = rootDiagUnit .F4 a) :
    Subgroup.centralizer ({b} : Set (adjointGroup .F4 K)) =
      (toralCentralizer .F4 K a).subgroupOf (adjointGroup .F4 K) := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, mem_toralCentralizer, ← hb,
    mul_inv_eq_iff_eq_mul]
  constructor
  · intro h
    exact ⟨g.2, (congrArg Subtype.val h).symm⟩
  · rintro ⟨-, h⟩
    exact Subtype.ext h.symm

theorem isComponentOf_B2Levi
    [Finite K] [CharP K 2]
    (hq : 4 ≤ Nat.card K) {a : Fin Tag.F4.rank → Kˣ} (ha : rootCharKernel a = b2LeviRoots)
    {b : adjointGroup .F4 K} (hb : (b : ModGL .F4 K) = rootDiagUnit .F4 a) :
    IsComponentOf (B2Levi K) (Subgroup.centralizer ({b} : Set (adjointGroup .F4 K))) := by
  obtain ⟨hMX, hMXn, -⟩ := Chevalley_toral_centralizer_root_generated_quotient .F4 K a
  have hM : toralRootGroup .F4 K a = torusGroup .F4 K ⊔ rootSpan .F4 K b2LeviRoots := by
    rw [toralRootGroup, ha]
  have hLM : rootSpan .F4 K b2LeviRoots ≤ toralRootGroup .F4 K a := hM ▸ le_sup_right
  have hLMn : ((rootSpan .F4 K b2LeviRoots).subgroupOf (toralRootGroup .F4 K a)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hLM, hM]
    exact sup_le (torusGroup_le_normalizer_rootSpan fun α hα => (mem_b2LeviRoots.1 hα).1)
      Subgroup.le_normalizer
  rw [centralizer_eq_toralCentralizer hb]
  have h1 : B2Levi K ≤ (toralRootGroup .F4 K a).subgroupOf (adjointGroup .F4 K) := fun x hx =>
    Subgroup.mem_subgroupOf.2 (hLM (mem_B2Levi_iff.1 hx))
  have h2 : (toralRootGroup .F4 K a).subgroupOf (adjointGroup .F4 K) ≤
      (toralCentralizer .F4 K a).subgroupOf (adjointGroup .F4 K) := fun x hx =>
    Subgroup.mem_subgroupOf.2 (hMX (Subgroup.mem_subgroupOf.1 hx))
  refine ⟨h1.trans h2, IsSubnormal.step h1 (normal_subgroupOf_subgroupOf hLM hLMn)
    (IsSubnormal.step h2 (normal_subgroupOf_subgroupOf hMX hMXn) (IsSubnormal.refl _)), ?_⟩
  exact isQuasisimple_of_isSimpleGroup (isSimpleGroup_B2Levi hq) center_B2Levi_eq_bot

end Component

section Count

variable {K : Type} [Field K]

theorem pinnedX_mem_B2Levi
    {γ : Fin Tag.F4.rank → ℤ} (hγ : γ ∈ b2LeviRoots) (c : K) :
    (⟨pinnedX .F4 K γ c, pinnedX_mem_adjointGroup γ c⟩ : adjointGroup .F4 K) ∈ B2Levi K :=
  mem_B2Levi_iff.2 (le_iSup₂ (f := fun γ (_ : γ ∈ b2LeviRoots) => rootSubgroup .F4 K γ) γ hγ
    (Subgroup.subset_closure ⟨c, rfl⟩))

theorem card_torusPow_inf_centralizer_B2Levi_le
    {p : ℕ} (hp : p.Prime)
    {w : Kˣ} (hw : orderOf w = p) :
    Nat.card (TableBF4.torusPow K p ⊓ Subgroup.centralizer (B2Levi K : Set (adjointGroup .F4 K)) :
      Subgroup (adjointGroup .F4 K)) ≤ p ^ 2 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  let f : ZMod p × ZMod p → adjointGroup .F4 K := fun st =>
    ⟨rootDiagUnit .F4
        (fun i => w ^ ((if i = 0 then st.1 else 0) + (if i = 3 then st.2 else 0)).val),
      f4RootDiagUnit_mem_adjointGroup _⟩
  have hsub : ((TableBF4.torusPow K p ⊓ Subgroup.centralizer (B2Levi K : Set (adjointGroup .F4 K)) :
      Subgroup (adjointGroup .F4 K)) : Set (adjointGroup .F4 K)) ⊆ Set.range f := by
    rintro s ⟨hsV, hsC⟩
    have hsV' : (s : ModGL .F4 K) ∈ {h : ModGL .F4 K | h ∈ torusGroup .F4 K ∧ h ^ p = 1} :=
      ⟨hsV.1, by rw [← Subgroup.coe_pow, hsV.2, OneMemClass.coe_one]⟩
    obtain ⟨x, -, hx⟩ :=
      (CFSG.RankThree.Chevalley.F4_bijOn_rootDiagUnit_pow_val (k := K) hw).2.2 hsV'
    have hx' : rootDiagUnit .F4 (fun j => w ^ (x j).val) = (s : ModGL .F4 K) := hx
    have hxi : ∀ i : Fin Tag.F4.rank, i ≠ 0 → i ≠ 3 → x i = 0 := by
      intro i hi0 hi3
      have hγ : (Pi.single i 1 : Fin Tag.F4.rank → ℤ) ∈ b2LeviRoots :=
        mem_b2LeviRoots.2 ⟨isRoot_single .F4 i, Pi.single_eq_of_ne (Ne.symm hi0) _,
          Pi.single_eq_of_ne (Ne.symm hi3) _⟩
      have hc := Subgroup.mem_centralizer_iff.1 hsC _ (pinnedX_mem_B2Levi hγ 1)
      have hc' : (s : ModGL .F4 K) * pinnedX .F4 K (Pi.single i 1) 1 =
          pinnedX .F4 K (Pi.single i 1) 1 * (s : ModGL .F4 K) := (congrArg Subtype.val hc).symm
      have hconj := rootDiagUnit_conj_pinnedX (fun j => w ^ (x j).val) (isRoot_single .F4 i)
        (1 : K)
      rw [hx', hc', mul_inv_cancel_right, mul_one, TableBF4.rootChar_single_F4] at hconj
      have h4 := pinnedX_injective .F4 K (Pi.single i 1) hconj
      have h5 : w ^ (x i).val = 1 := Units.ext (by rw [Units.val_one]; exact h4.symm)
      have h6 := orderOf_dvd_of_pow_eq_one h5
      rw [hw] at h6
      exact (ZMod.val_eq_zero _).mp (Nat.eq_zero_of_dvd_of_lt h6 (ZMod.val_lt _))
    refine ⟨(x 0, x 3), Subtype.ext ?_⟩
    change rootDiagUnit .F4 _ = (s : ModGL .F4 K)
    rw [← hx']
    congr 1
    funext i
    congr 2
    by_cases h0 : i = 0
    · subst h0
      simp
    by_cases h3 : i = 3
    · subst h3
      simp
    simp [h0, h3, hxi i h0 h3]
  calc Nat.card (TableBF4.torusPow K p ⊓
        Subgroup.centralizer (B2Levi K : Set (adjointGroup .F4 K)) : Subgroup (adjointGroup .F4 K))
      ≤ Nat.card (Set.range f) := Nat.card_mono (Set.finite_range f) hsub
    _ ≤ Nat.card (ZMod p × ZMod p) := Finite.card_range_le f
    _ = p ^ 2 := by rw [Nat.card_prod, Nat.card_zmod, sq]

end Count

section Main

theorem map_conj_centralizer_singleton {G : Type*} [Group G] (g b : G) :
    (Subgroup.centralizer ({b} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({g * b * g⁻¹} : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * y * g⁻¹ * (g * b * g⁻¹) = g * (y * b) * g⁻¹ := by group
      _ = g * (b * y) * g⁻¹ := by rw [hy]
      _ = g * b * g⁻¹ * (g * y * g⁻¹) := by group
  · intro hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      calc g⁻¹ * x * g * b = g⁻¹ * (x * (g * b * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * b * g⁻¹) * x) * g := by rw [hx]
        _ = b * (g⁻¹ * x * g) := by group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

theorem map_conj_centralizer {G : Type*} [Group G] (g : G) (L : Subgroup G) :
    (Subgroup.centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨l, hl, rfl⟩
    have h := Subgroup.mem_centralizer_iff.1 hy l hl
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * l * g⁻¹ * (g * y * g⁻¹) = g * (l * y) * g⁻¹ := by group
      _ = g * (y * l) * g⁻¹ := by rw [h]
      _ = g * y * g⁻¹ * (g * l * g⁻¹) := by group
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro l hl
      have h := Subgroup.mem_centralizer_iff.1 hx (g * l * g⁻¹) ⟨l, hl, rfl⟩
      calc l * (g⁻¹ * x * g) = g⁻¹ * ((g * l * g⁻¹) * x) * g := by group
        _ = g⁻¹ * (x * (g * l * g⁻¹)) * g := by rw [h]
        _ = g⁻¹ * x * g * l := by group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

theorem wu_pow_eq_one {G : Type*} [CommGroup G] {w u : G} {p : ℕ} (hw : w ^ p = 1)
    (hu : u ^ p = 1) (a b : ℤ) : (w ^ a * u ^ b) ^ p = 1 := by
  rw [mul_pow, ← zpow_natCast, ← zpow_natCast (u ^ b), ← zpow_mul, ← zpow_mul, mul_comm a,
    mul_comm b, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hw, hu, one_zpow, one_zpow,
    one_mul]

theorem not_three_dvd (m : ℕ) : ¬ 3 ∣ 2 ^ (2 * m + 1) - 1 := by
  have h : 2 ^ (2 * m + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  generalize 2 ^ (2 * m + 1) = N at h ⊢
  omega

end Main

end F4Rest

end CFSG.StandardType
