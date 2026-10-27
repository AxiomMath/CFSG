module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3Core
public import CFSG.LieType.SteinbergBRAutGL32
public import CFSG.RankThree.PartOne.Q1327T.Perm3
import CFSG.Mathlib.GroupTheory.PermCommute

public section

namespace CFSG.Quasithin.Fan86.Sigma3

open CFSG.Open

variable {H : Type*} [Group H] [Finite H] {S : Subgroup H}

omit [Finite H] in
theorem sqClosure_char : (Subgroup.closure {w : ↥S | ∃ s : ↥S, w = s * s}).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  rw [MonoidHom.map_closure]
  apply Subgroup.closure_mono
  rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
  exact ⟨φ s, by simp⟩

theorem sqClosure_le_Q (h : Sig3 H S) :
    Subgroup.closure {w : ↥S | ∃ s : ↥S, w = s * s} ≤
      (CFSG.Open.pCore 2 H).subgroupOf S := by
  rw [Subgroup.closure_le]
  rintro _ ⟨s, rfl⟩
  exact h.sq_mem s.2

theorem Sig3.sq_eq_one_of_central (h : Sig3 H S) {x : H} (hx : orderOf x = 3)
    (hQx : ∀ q ∈ CFSG.Open.pCore 2 H, x * q = q * x)
    (hno : ∀ K : Subgroup H, K ≤ S → (K.subgroupOf S).Characteristic → K.Normal → K = ⊥) :
    ∀ s ∈ S, s * s = 1 := by
  set KS : Subgroup ↥S := Subgroup.closure {w : ↥S | ∃ s : ↥S, w = s * s} with hKS
  have : KS.Characteristic := sqClosure_char
  set K : Subgroup H := KS.map S.subtype with hK
  have hKsub : K.subgroupOf S = KS := Subgroup.comap_map_eq_self_of_injective S.subtype_injective KS
  have hKS' : K ≤ S := Subgroup.map_subtype_le _
  have hKQ : ∀ k ∈ K, k ∈ CFSG.Open.pCore 2 H := by
    rintro _ ⟨t, ht, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (sqClosure_le_Q h ht)
  have hSn : ∀ s ∈ S, ∀ k ∈ K, s * k * s⁻¹ ∈ K := by
    rintro s hs _ ⟨t, ht, rfl⟩
    exact ⟨⟨s, hs⟩ * t * ⟨s, hs⟩⁻¹, (inferInstance : KS.Normal).conj_mem t ht ⟨s, hs⟩, by simp⟩
  have hxn : ∀ k ∈ K, x * k * x⁻¹ = k := fun k hk => by
    rw [hQx k (hKQ k hk)]; group
  have hxn' : ∀ k ∈ K, x⁻¹ * k * x = k := fun k hk => by
    have := hQx k (hKQ k hk)
    calc x⁻¹ * k * x = x⁻¹ * (k * x) := by group
      _ = x⁻¹ * (x * k) := by rw [this]
      _ = k := by group
  have hnorm : K.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
    intro g _
    have hg : g ∈ S ⊔ Subgroup.zpowers x := h.gen hx ▸ Subgroup.mem_top g
    refine (sup_le ?_ ?_ : S ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer (K : Set H)) hg
    · intro s hs
      refine Subgroup.mem_normalizer_iff.2 fun k => ⟨fun hk => hSn s hs k hk, fun hk => ?_⟩
      have := hSn s⁻¹ (S.inv_mem hs) _ hk
      have e : s⁻¹ * (s * k * s⁻¹) * s⁻¹⁻¹ = k := by group
      rwa [e] at this
    · refine Subgroup.zpowers_le.2
        (Subgroup.mem_normalizer_iff.2 fun k => ⟨fun hk => ?_, fun hk => ?_⟩)
      · rw [hxn k hk]; exact hk
      · have hkQ : k ∈ CFSG.Open.pCore 2 H := by
          have := (inferInstance : (CFSG.Open.pCore 2 H).Normal).conj_mem _ (hKQ _ hk) x⁻¹
          have e : x⁻¹ * (x * k * x⁻¹) * x⁻¹⁻¹ = k := by group
          rwa [e] at this
        have hk' : x * k * x⁻¹ = k := by rw [hQx k hkQ]; group
        rwa [hk'] at hk
  have hKbot : K = ⊥ := hno K hKS' (by rw [hKsub]; infer_instance) hnorm
  have hKSbot : KS = ⊥ := by rw [← hKsub, hKbot, Subgroup.bot_subgroupOf]
  intro s hs
  have : (⟨s, hs⟩ : ↥S) * ⟨s, hs⟩ ∈ KS := Subgroup.subset_closure ⟨⟨s, hs⟩, rfl⟩
  rw [hKSbot, Subgroup.mem_bot] at this
  exact congrArg Subtype.val this

theorem Sig3.case_central (h : Sig3 H S) {x : H} (hx : orderOf x = 3)
    (hQx : ∀ q ∈ CFSG.Open.pCore 2 H, x * q = q * x)
    (hno : ∀ K : Subgroup H, K ≤ S → (K.subgroupOf S).Characteristic → K.Normal → K = ⊥) :
    ∃ T E : Subgroup H, Nonempty (↥T ≃* Equiv.Perm (Fin 3)) ∧ CFSG.Open.IsElemAbelian 2 E ∧
      (∀ t ∈ T, ∀ e ∈ E, t * e = e * t) ∧ T ⊓ E = ⊥ ∧ T ⊔ E = ⊤ := by
  have hsq := h.sq_eq_one_of_central hx hQx hno
  have hinv : ∀ s ∈ S, s⁻¹ = s := fun s hs => inv_eq_of_mul_eq_one_right (hsq s hs)
  have hSab : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s := by
    intro s hs t ht
    have h1 := hsq (s * t) (S.mul_mem hs ht)
    have h2 : s * t = (s * t)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    rwa [mul_inv_rev, hinv s hs, hinv t ht] at h2
  obtain ⟨a, haS, haQ⟩ := h.exists_a
  have ha2 : a * a = 1 := hsq a haS
  obtain ⟨q, hq, hqeq⟩ := h.inv_mod hx haS haQ
  have hqS : q ∈ S := h.Q_le_S hq
  have hq1 : q = 1 := by
    have hc : Commute q x⁻¹ := ((hQx q hq).symm : q * x = x * q) |> fun h' => (Commute.inv_right h')
    have h3 : (q * x⁻¹) ^ 3 = 1 := by
      rw [← hqeq, conj_pow]
      have : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
      rw [this]; group
    rw [hc.mul_pow, inv_pow] at h3
    have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    rw [hx3, inv_one, mul_one] at h3
    have h4 : q ^ 3 = q := by
      rw [show q ^ 3 = q * q * q by rw [pow_succ, pow_two], hsq q hqS, one_mul]
    rw [← h4]; exact h3
  have hax : a * x * a⁻¹ = x⁻¹ := by rw [hqeq, hq1, one_mul]
  have hnot : a ∉ Subgroup.zpowers x := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have h1 : x ^ (2 * k) = 1 := by
      rw [mul_comm, zpow_mul, hk, zpow_two, ha2]
    have h2 := orderOf_dvd_iff_zpow_eq_one.2 h1
    rw [hx] at h2
    have h3 : ((3 : ℕ) : ℤ) ∣ k := by push_cast at h2 ⊢; omega
    have : a = 1 := by
      rw [← hk]
      exact orderOf_dvd_iff_zpow_eq_one.1 (by rw [hx]; exact h3)
    exact haQ (this ▸ (CFSG.Open.pCore 2 H).one_mem)
  obtain ⟨e1⟩ := CFSG.LieType.SteinbergBR.AutGL32.nonempty_closure_pair_mulEquiv_dihedralGroup
    (ρ := x) (σ := a) (by rw [pow_two]; exact ha2) hax hnot
  rw [hx] at e1
  set T : Subgroup H := Subgroup.closure ({x, a} : Set H) with hT
  set eT : ↥T ≃* Equiv.Perm (Fin 3) := e1.trans CFSG.RankThree.PartOne.Q1327T.d3EquivPerm with heT
  have hxT : x ∈ T := Subgroup.subset_closure (by simp)
  have haT : a ∈ T := Subgroup.subset_closure (by simp)
  have hTE : ∀ t ∈ T, ∀ e ∈ CFSG.Open.pCore 2 H, t * e = e * t := by
    intro t ht e he
    have : T ≤ Subgroup.centralizer {e} := by
      rw [hT, Subgroup.closure_le]
      rintro g (rfl | rfl)
      · exact Subgroup.mem_centralizer_iff.2 fun z hz => by
          rw [Set.mem_singleton_iff.1 hz]; exact (hQx e he).symm
      · exact Subgroup.mem_centralizer_iff.2 fun z hz => by
          rw [Set.mem_singleton_iff.1 hz]; exact (hSab _ (h.Q_le_S he) _ haS)
    exact (Subgroup.mem_centralizer_iff.1 (this ht) e rfl).symm
  refine ⟨T, CFSG.Open.pCore 2 H, ⟨eT⟩, ⟨⟨⟨fun u v => Subtype.ext
      (hSab u (h.Q_le_S u.2) v (h.Q_le_S v.2))⟩⟩, fun y hy => ?_⟩, hTE, ?_, ?_⟩
  · rw [pow_two]; exact hsq y (h.Q_le_S hy)
  · rw [eq_bot_iff]
    rintro y ⟨hyT, hyE⟩
    have hc : ∀ z : ↥T, (⟨y, hyT⟩ : ↥T) * z = z * ⟨y, hyT⟩ := fun z =>
      Subtype.ext (hTE z z.2 y hyE).symm
    have h1 : eT ⟨y, hyT⟩ = 1 := CFSG.perm_eq_one_of_forall_commute (by simp) fun τ => by
      obtain ⟨z, rfl⟩ := eT.surjective τ
      rw [← map_mul, ← map_mul, hc z]
    have h2 : (⟨y, hyT⟩ : ↥T) = 1 := (map_eq_one_iff eT eT.injective).1 h1
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val h2)
  · rw [eq_top_iff, ← h.gen hx]
    refine sup_le ?_ (Subgroup.zpowers_le.2 (Subgroup.mem_sup_left hxT))
    intro s hs
    rcases h.mul_inv_mem hs haS haQ with h1 | h1
    · exact Subgroup.mem_sup_right h1
    · have : s = (s * a⁻¹) * a := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left haT)

end CFSG.Quasithin.Fan86.Sigma3
