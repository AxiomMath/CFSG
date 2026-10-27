module

public import CFSG.Quasithin.EmptyFaithful.S153VIz

public section

namespace CFSG.Quasithin.ModF

open scoped Pointwise commutatorElement
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Lin2 CFSG.LieType.BorelTits
  CFSG.Quasithin.ModV CFSG.QuasithinUnique.A5.Delta5 Equiv

variable {G : Type} [Group G] [Finite G] {I S Iz K₁ K₂ : Subgroup G}

noncomputable def zel {L : Subgroup G} (P : AppC.A5Pi L) (p : Fin 5) : G :=
  Classical.choose (P.toPiData.bf_surj ⟨zvec p, (mem_evenWeight_iff _).mpr (isEven_zvec p)⟩)

omit [Finite G] in
theorem zel_mem {L : Subgroup G} (P : AppC.A5Pi L) (p : Fin 5) : zel P p ∈ blockU L :=
  (Classical.choose_spec (P.toPiData.bf_surj
    ⟨zvec p, (mem_evenWeight_iff _).mpr (isEven_zvec p)⟩)).1

omit [Finite G] in
theorem bf_zel {L : Subgroup G} (P : AppC.A5Pi L) (p : Fin 5) :
    P.toPiData.bf (zel P p) = ⟨zvec p, (mem_evenWeight_iff _).mpr (isEven_zvec p)⟩ :=
  (Classical.choose_spec (P.toPiData.bf_surj
    ⟨zvec p, (mem_evenWeight_iff _).mpr (isEven_zvec p)⟩)).2

omit [Finite G] in
theorem mem_centralizer_sup_of {d : G} (h₁ : ∀ x ∈ K₁, x * d = d * x)
    (h₂ : ∀ x ∈ K₂, x * d = d * x) :
    d ∈ Subgroup.centralizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) := by
  have hle : K₁ ⊔ K₂ ≤ Subgroup.centralizer ({d} : Set G) := by
    refine sup_le (fun x hx => Subgroup.mem_centralizer_iff.mpr fun h hh => ?_)
      (fun x hx => Subgroup.mem_centralizer_iff.mpr fun h hh => ?_)
    · rw [Set.mem_singleton_iff.mp hh]
      exact (h₁ x hx).symm
    · rw [Set.mem_singleton_iff.mp hh]
      exact (h₂ x hx).symm
  exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
    (Subgroup.mem_centralizer_iff.mp (hle hx) d rfl).symm

namespace A5Cfg

variable (c : A5Cfg I S Iz K₁ K₂)
include c

theorem exists_U_mul_D {q : G} (hq : q ∈ blockQ K₁) :
    ∃ u ∈ blockU K₁, ∃ d ∈ dsub S K₁ K₂, q = u * d := by
  obtain ⟨α, hα, hαk, -⟩ := c.a5₁
  obtain ⟨P, -⟩ := AppC.exists_a5pi c.blk₁.1 c.a5₁ α hα hαk
  have hbb : ∀ ℓ ∈ K₁, q * ℓ * q⁻¹ * ℓ⁻¹ ∈ blockU K₁ := fun ℓ hℓ => C1.commutator_mem_blockU hq hℓ
  have hqC : ∀ u ∈ blockU K₁, q * u = u * q := fun u hu =>
    (C1.blockU_comm c.blk₁.1 u hu q hq).symm
  obtain ⟨u, hu, hcent⟩ := AppCS2.exists_split_abs c.blk₁.1 c.a5₁ P hbb hqC
  have huQ : u ∈ blockQ K₁ := C1.blockU_le_blockQ c.blk₁.1 hu
  have hdQ : u * q ∈ blockQ K₁ := (blockQ K₁).mul_mem huQ hq
  have hdK : u * q ∈ K₁ := C1.blockQ_le K₁ hdQ
  refine ⟨u⁻¹, inv_mem hu, u * q, ⟨(c.pCore_le₁ hdQ).1, mem_centralizer_sup_of hcent ?_⟩, by group⟩
  intro x hx
  exact (c.comm (u * q) hdK x hx).symm

theorem central_mem_of_sub (P : AppC.A5Pi K₁) {p : Fin 5} (hp : ∀ g ∈ imgS K₁ S P.α, g p = p)
    {T : Subgroup G} (hTS : T ≤ S ⊓ K₁)
    (hT2 : ∀ v ∈ klein p, ∃ y ∈ T, P.toPiData.pf y = v)
    (hT3 : ∀ v ∈ klein p, v ≠ 1 → ∃ u ∈ T, u ∈ blockU K₁ ∧
      vact v (P.toPiData.bf u) ≠ P.toPiData.bf u)
    {r : G} (hrT : r ∈ T) (hr : ∀ t ∈ T, r * t = t * r) :
    r ∈ dsub S K₁ K₂ ⊔ Subgroup.zpowers (zel P p) := by
  have hrSK := hTS hrT
  have hrN : r ∈ Subgroup.normalizer (K₁ : Set G) := Subgroup.le_normalizer hrSK.2
  have hpfr : P.toPiData.pf r ∈ klein p := by
    rw [pf_eq_alpha P hrSK.2, ← toPerm_apply]
    exact (c.memS_iff P hp ⟨r, hrSK.2⟩).mp hrSK.1
  have hpf1 : P.toPiData.pf r = 1 := by
    by_contra hne
    obtain ⟨u, huT, huU, hu⟩ := hT3 _ hpfr hne
    exact hu ((P.toPiData.comm_iff hrN huU).mp (hr u huT))
  have hrQ : r ∈ blockQ K₁ := by
    have h1 : P.α ⟨r, hrSK.2⟩ = 1 := by
      have : ((P.α ⟨r, hrSK.2⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5)) = 1 := by
        rw [← pf_eq_alpha P hrSK.2]
        exact hpf1
      exact Subtype.ext this
    have h2 : (⟨r, hrSK.2⟩ : ↥K₁) ∈ CFSG.pCore 2 ↥K₁ := by rw [← P.hαk]; exact h1
    exact (AppC.mem_pCore_iff_mem_blockQ _).mp h2
  obtain ⟨u, hu, d, hd, hrud⟩ := c.exists_U_mul_D hrQ
  have huc : ∀ t ∈ T, u * t = t * u := by
    intro t ht
    have hdt : d * t = t * d :=
      (K_le_centralizer_dsub t (Subgroup.mem_sup_left (hTS ht).2) d hd).symm
    have hrt := hr t ht
    rw [hrud] at hrt
    have h1 : (u * t) * d = (t * u) * d := by
      calc (u * t) * d = u * (t * d) := by group
        _ = u * (d * t) := by rw [hdt]
        _ = (u * d) * t := by group
        _ = t * (u * d) := hrt
        _ = (t * u) * d := by group
    exact mul_right_cancel h1
  have hfix : ∀ v ∈ klein p, pact v (P.toPiData.bf u).1 = (P.toPiData.bf u).1 := by
    intro v hv
    obtain ⟨y, hyT, hy⟩ := hT2 v hv
    have hyN : y ∈ Subgroup.normalizer (K₁ : Set G) := Subgroup.le_normalizer (hTS hyT).2
    have := (P.toPiData.comm_iff hyN hu).mp (huc y hyT).symm
    rw [hy] at this
    exact congrArg Subtype.val this
  rcases fix_klein p _ ((mem_evenWeight_iff _).mp (P.toPiData.bf u).2) hfix with h0 | hz
  · have hu1 : u = 1 := by
      apply P.toPiData.bf_inj hu (one_mem _)
      rw [P.toPiData.bf_one]
      exact Subtype.ext h0
    rw [hrud, hu1, one_mul]
    exact Subgroup.mem_sup_left hd
  · have huz : u = zel P p := by
      apply P.toPiData.bf_inj hu (zel_mem P p)
      rw [bf_zel]
      exact Subtype.ext hz
    rw [hrud, huz]
    exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) (Subgroup.mem_sup_left hd)

omit c in
theorem exists_odd_power (g : G) : ∃ k : ℕ, Odd (orderOf (g ^ k)) ∧ k % 3 = 1 := by
  have hpos : orderOf g ≠ 0 := (orderOf_pos g).ne'
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd hpos
  obtain ⟨k, hk0, hk1⟩ :=
    Nat.chineseRemainder (Nat.Coprime.pow_left a (by norm_num : Nat.Coprime 2 3)) 0 1
  refine ⟨k, ?_, ?_⟩
  · have hdvd : orderOf (g ^ k) ∣ m := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul]
      apply orderOf_dvd_iff_pow_eq_one.mp
      rw [hn]
      exact Nat.mul_dvd_mul_right (Nat.modEq_zero_iff_dvd.mp hk0) m
    exact hm.of_dvd_nat hdvd
  · simpa [Nat.ModEq] using hk1

theorem exists_odd_lift (P : AppC.A5Pi K₁) {p : Fin 5} (hp : ∀ g ∈ imgS K₁ S P.α, g p = p)
    {γ : Perm (Fin 5)} (hγs : Perm.sign γ = 1) (hγp : γ p = p) (hγ3 : γ ^ 3 = 1) :
    ∃ x ∈ oTwoUpper Iz ⊓ K₁, P.toPiData.pf x = γ := by
  obtain ⟨g, hg⟩ := exists_lift P γ hγs
  have hgIz := c.lift_mem_Iz P hp hγp g hg
  obtain ⟨k, hodd, hk3⟩ := exists_odd_power (g : G)
  have hN : (g : G) ∈ Subgroup.normalizer (K₁ : Set G) := Subgroup.le_normalizer g.2
  have hgk : (g : G) ^ k ∈ Subgroup.normalizer (K₁ : Set G) := (Subgroup.normalizer _).pow_mem hN k
  refine ⟨(g : G) ^ k, ⟨mem_oTwoUpper_of_odd (Iz.pow_mem hgIz k) hodd, K₁.pow_mem g.2 k⟩, ?_⟩
  rw [P.toPiData.pf_eq hgk]
  have e : (⟨(g : G) ^ k, hgk⟩ : ↥(Subgroup.normalizer (K₁ : Set G))) = ⟨(g : G), hN⟩ ^ k := rfl
  have hπ : P.π ⟨(g : G), hN⟩ = γ := by
    rw [← P.toPiData.pf_eq hN, pf_eq_alpha P g.2]
    have : (⟨(g : G), g.2⟩ : ↥K₁) = g := rfl
    rw [this, ← toPerm_apply, hg]
  rw [e, map_pow, hπ, pow_eq_pow_mod k hγ3, hk3, pow_one]

theorem R_inf_le : pCoreOf 2 (oTwoUpper Iz ⊓ K₁) ≤ S ⊓ K₁ := by
  have hX_le : oTwoUpper Iz ⊓ K₁ ≤ Iz ⊓ K₁ := inf_le_inf_right _ (oTwoUpper_le Iz)
  have hnormX : ∀ g ∈ Iz ⊓ K₁, g ∈ Subgroup.normalizer ((oTwoUpper Iz ⊓ K₁ : Subgroup G) : Set G) :=
    fun g hg => C5.mem_normalizer_inf (le_normalizer_oTwoUpper Iz hg.1) (Subgroup.le_normalizer hg.2)
  have hR : pCoreOf 2 (oTwoUpper Iz ⊓ K₁) ≤ pCoreOf 2 (Iz ⊓ K₁) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans hX_le)
      (fun g hg => C1.mem_normalizer_blockQ (hnormX g hg)) (pCoreOf_isPGroup 2 _)
  have hsyl : IsSylowTwoOf (S ⊓ K₁) (Iz ⊓ K₁) :=
    B6.isSylowTwoOf_mono c.sylow₁ (inf_le_inf_right K₁ c.S_le_Iz) inf_le_right
  exact hR.trans (B6.pCoreOf_two_le_of_isSylowTwoOf hsyl)

theorem X_inf_S_le_R (P : AppC.A5Pi K₁) {p : Fin 5} (hp : ∀ g ∈ imgS K₁ S P.α, g p = p)
    (hnot : ¬ K₁ ≤ Iz) :
    (oTwoUpper Iz ⊓ K₁) ⊓ (S ⊓ K₁) ≤ pCoreOf 2 (oTwoUpper Iz ⊓ K₁) := by
  refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
    (c.sylow.isPGroup.to_le (inf_le_right.trans inf_le_left))
  intro x hx
  exact C5.mem_normalizer_inf (Subgroup.le_normalizer hx)
    (c.inf_Iz_le_normalizer P hp hnot x hx.2 ((oTwoUpper_le Iz) hx.1))

omit [Finite G] c in
theorem comm_mem_U {u x : G} (hu : u ∈ blockU K₁) (hx : x ∈ K₁) :
    u * x * u⁻¹ * x⁻¹ ∈ blockU K₁ := by
  have h1 : x * u⁻¹ * x⁻¹ ∈ blockU K₁ :=
    (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU (Subgroup.le_normalizer hx)) u⁻¹).mp
      (inv_mem hu)
  have e : u * x * u⁻¹ * x⁻¹ = u * (x * u⁻¹ * x⁻¹) := by group
  rw [e]
  exact mul_mem hu h1

theorem comm_mem_R (P : AppC.A5Pi K₁) {p : Fin 5} (hp : ∀ g ∈ imgS K₁ S P.α, g p = p)
    (hnot : ¬ K₁ ≤ Iz) {u x : G} (hu : u ∈ blockU K₁) (hx : x ∈ oTwoUpper Iz ⊓ K₁) :
    u * x * u⁻¹ * x⁻¹ ∈ pCoreOf 2 (oTwoUpper Iz ⊓ K₁) := by
  have heU := comm_mem_U (K₁ := K₁) hu hx.2
  have huIz : u ∈ Iz := c.S_le_Iz (c.pCore_le₁ (C1.blockU_le_blockQ c.blk₁.1 hu)).1
  have huK : u ∈ K₁ := c.U₁_le_K₁ hu
  have hn : u ∈ Subgroup.normalizer ((oTwoUpper Iz ⊓ K₁ : Subgroup G) : Set G) :=
    C5.mem_normalizer_inf (le_normalizer_oTwoUpper Iz huIz) (Subgroup.le_normalizer huK)
  have hux : u * x * u⁻¹ ∈ oTwoUpper Iz ⊓ K₁ := (Subgroup.mem_normalizer_iff.mp hn x).mp hx
  refine c.X_inf_S_le_R P hp hnot ⟨(oTwoUpper Iz ⊓ K₁).mul_mem hux ((oTwoUpper Iz ⊓ K₁).inv_mem hx), ?_, c.U₁_le_K₁ heU⟩
  exact (c.pCore_le₁ (C1.blockU_le_blockQ c.blk₁.1 heU)).1

theorem bf_comm (P : AppC.A5Pi K₁) {u x : G} (hu : u ∈ blockU K₁) (hx : x ∈ K₁) :
    (P.toPiData.bf (u * x * u⁻¹ * x⁻¹)).1 =
      (P.toPiData.bf u).1 + pact (P.toPiData.pf x) (P.toPiData.bf u).1 := by
  have hxN : x ∈ Subgroup.normalizer (K₁ : Set G) := Subgroup.le_normalizer hx
  have hu2 : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact C1.blockU_sq c.blk₁.1 u hu)
  have hw : x * u⁻¹ * x⁻¹ ∈ blockU K₁ :=
    (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU hxN) u⁻¹).mp (inv_mem hu)
  have e : u * x * u⁻¹ * x⁻¹ = u * (x * u⁻¹ * x⁻¹) := by group
  rw [e, P.toPiData.bf_mul hu hw, P.toPiData.bf_conj hxN (inv_mem hu), hu2]
  rfl

theorem pf_surj_R (P : AppC.A5Pi K₁) {p : Fin 5} (hp : ∀ g ∈ imgS K₁ S P.α, g p = p)
    (hnot : ¬ K₁ ≤ Iz) :
    ∀ v ∈ klein p, ∃ y ∈ pCoreOf 2 (oTwoUpper Iz ⊓ K₁), P.toPiData.pf y = v := by
  intro v hv
  obtain ⟨c₁, c₂, hs₁, hp₁, h3₁, hs₂, hp₂, h3₂, rfl⟩ := klein_eq_mul p v hv
  obtain ⟨x₁, hx₁, hpf₁⟩ := c.exists_odd_lift P hp hs₁ hp₁ h3₁
  obtain ⟨x₂, hx₂, hpf₂⟩ := c.exists_odd_lift P hp hs₂ hp₂ h3₂
  have hy : x₁ * x₂ ∈ oTwoUpper Iz ⊓ K₁ := mul_mem hx₁ hx₂
  have hN₁ : x₁ ∈ Subgroup.normalizer (K₁ : Set G) := Subgroup.le_normalizer hx₁.2
  have hN₂ : x₂ ∈ Subgroup.normalizer (K₁ : Set G) := Subgroup.le_normalizer hx₂.2
  have hpf : P.toPiData.pf (x₁ * x₂) = c₁ * c₂ := by
    rw [P.toPiData.pf_mul hN₁ hN₂, hpf₁, hpf₂]
  have e : toPerm P.α ⟨x₁ * x₂, hy.2⟩ = P.toPiData.pf (x₁ * x₂) := by
    rw [pf_eq_alpha P hy.2, toPerm_apply]
  have hS : x₁ * x₂ ∈ S := (c.memS_iff P hp ⟨x₁ * x₂, hy.2⟩).mpr (by rw [e, hpf]; exact hv)
  exact ⟨x₁ * x₂, c.X_inf_S_le_R P hp hnot ⟨hy, hS, hy.2⟩, hpf⟩

theorem noFix_R (P : AppC.A5Pi K₁) {p : Fin 5} (hp : ∀ g ∈ imgS K₁ S P.α, g p = p)
    (hnot : ¬ K₁ ≤ Iz) : ∀ v ∈ klein p, v ≠ 1 →
    ∃ u ∈ pCoreOf 2 (oTwoUpper Iz ⊓ K₁), u ∈ blockU K₁ ∧
      vact v (P.toPiData.bf u) ≠ P.toPiData.bf u := by
  intro v hv hv1
  obtain ⟨γ, w, hγs, hγp, hγ3, hw, hne⟩ := exists_noFix p v hv hv1
  obtain ⟨u', hu', hbu'⟩ := P.toPiData.bf_surj ⟨w, (mem_evenWeight_iff _).mpr hw⟩
  obtain ⟨x, hx, hpfx⟩ := c.exists_odd_lift P hp hγs hγp hγ3
  refine ⟨u' * x * u'⁻¹ * x⁻¹, c.comm_mem_R P hp hnot hu' hx, comm_mem_U hu' hx.2, fun h => hne ?_⟩
  have h1 := congrArg Subtype.val h
  have h2 : (P.toPiData.bf (u' * x * u'⁻¹ * x⁻¹)).1 = w + pact γ w := by
    rw [c.bf_comm P hu' hx.2, hbu', hpfx]
  have h3 : pact v (P.toPiData.bf (u' * x * u'⁻¹ * x⁻¹)).1 = (P.toPiData.bf (u' * x * u'⁻¹ * x⁻¹)).1 := h1
  rwa [h2] at h3

theorem zel_mem_R (P : AppC.A5Pi K₁) {p : Fin 5} (hp : ∀ g ∈ imgS K₁ S P.α, g p = p)
    (hnot : ¬ K₁ ≤ Iz) : zel P p ∈ pCoreOf 2 (oTwoUpper Iz ⊓ K₁) := by
  obtain ⟨γ₁, γ₂, w₁, w₂, hs₁, hp₁, h3₁, hw₁, hs₂, hp₂, h3₂, hw₂, hsum⟩ := exists_zvec p
  obtain ⟨u₁, hu₁, hb₁⟩ := P.toPiData.bf_surj ⟨w₁, (mem_evenWeight_iff _).mpr hw₁⟩
  obtain ⟨u₂, hu₂, hb₂⟩ := P.toPiData.bf_surj ⟨w₂, (mem_evenWeight_iff _).mpr hw₂⟩
  obtain ⟨x₁, hx₁, hpf₁⟩ := c.exists_odd_lift P hp hs₁ hp₁ h3₁
  obtain ⟨x₂, hx₂, hpf₂⟩ := c.exists_odd_lift P hp hs₂ hp₂ h3₂
  have hU₁ := comm_mem_U (K₁ := K₁) hu₁ hx₁.2
  have hU₂ := comm_mem_U (K₁ := K₁) hu₂ hx₂.2
  have hR : (u₁ * x₁ * u₁⁻¹ * x₁⁻¹) * (u₂ * x₂ * u₂⁻¹ * x₂⁻¹) ∈ pCoreOf 2 (oTwoUpper Iz ⊓ K₁) :=
    mul_mem (c.comm_mem_R P hp hnot hu₁ hx₁) (c.comm_mem_R P hp hnot hu₂ hx₂)
  have hz : (u₁ * x₁ * u₁⁻¹ * x₁⁻¹) * (u₂ * x₂ * u₂⁻¹ * x₂⁻¹) = zel P p := by
    apply P.toPiData.bf_inj (mul_mem hU₁ hU₂) (zel_mem P p)
    rw [P.toPiData.bf_mul hU₁ hU₂, bf_zel]
    apply Subtype.ext
    show (P.toPiData.bf (u₁ * x₁ * u₁⁻¹ * x₁⁻¹)).1 + (P.toPiData.bf (u₂ * x₂ * u₂⁻¹ * x₂⁻¹)).1 = zvec p
    rw [c.bf_comm P hu₁ hx₁.2, c.bf_comm P hu₂ hx₂.2, hb₁, hb₂, hpf₁, hpf₂]
    exact hsum
  rw [← hz]
  exact hR

end A5Cfg

end CFSG.Quasithin.ModF
