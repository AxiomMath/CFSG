module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34SzComp
public import CFSG.Quasithin.Vol2.Ch1Comm

public section

namespace CFSG.Quasithin

open scoped commutatorElement

variable {W : Type} [CommGroup W]

private def szbKer (U : Subgroup W) : Subgroup (MulAut W) where
  carrier := {g | g ∈ stabSub U ∧ ∀ w : W, g w * w⁻¹ ∈ U}
  one_mem' := ⟨Subgroup.one_mem _, fun w => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨Subgroup.mul_mem _ ha hb, fun w => ?_⟩
    have e : (a * b) w * w⁻¹ = (a (b w) * (b w)⁻¹) * (b w * w⁻¹) := by
      rw [MulAut.mul_apply]
      group
    rw [e]
    exact U.mul_mem (ha' _) (hb' w)
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨Subgroup.inv_mem _ ha, fun w => ?_⟩
    have e : a⁻¹ w * w⁻¹ = (a (a⁻¹ w) * (a⁻¹ w)⁻¹)⁻¹ := by simp
    rw [e]
    exact U.inv_mem (ha' _)

private theorem szb_ker_conj {U : Subgroup W} {s g : MulAut W} (hs : s ∈ stabSub U)
    (hg : g ∈ szbKer U) : s * g * s⁻¹ ∈ szbKer U := by
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hs hg.1) (Subgroup.inv_mem _ hs), fun w => ?_⟩
  have e : (s * g * s⁻¹) w * w⁻¹ = s (g (s⁻¹ w) * (s⁻¹ w)⁻¹) := by
    simp [MulAut.mul_apply]
  rw [e]
  exact (hs _).mpr (hg.2 _)

private theorem szb_le_of_commutators {K N : Subgroup (MulAut W)} (hperf : ⁅K, K⁆ = K)
    (h : ∀ x ∈ K, ∀ y ∈ K, ⁅x, y⁆ ∈ N) : K ≤ N :=
  hperf.symm.le.trans (Subgroup.commutator_le.mpr h)

private theorem szb_comm_mul_of_commute {G : Type*} [Group G] {x' x y : G}
    (h : x' * y = y * x') : ⁅x', x * y⁆ = ⁅x', x⁆ := by
  have e : x' * y * x'⁻¹ = y := by rw [h]; group
  have e2 : y * x'⁻¹ = x'⁻¹ * y := by
    calc y * x'⁻¹ = x'⁻¹ * (x' * y * x'⁻¹) := by group
      _ = x'⁻¹ * y := by rw [e]
  calc ⁅x', x * y⁆ = x' * x * (y * x'⁻¹) * y⁻¹ * x⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = x' * x * (x'⁻¹ * y) * y⁻¹ * x⁻¹ := by rw [e2]
    _ = ⁅x', x⁆ := by simp only [commutatorElement_def]; group

variable [Finite W] in
theorem sz_ker_of_not_centralizes {X A K : Subgroup (MulAut W)} {U : Subgroup W}
    (hKc : K ∈ cComp X) (hKq : CFSG.IsQuasisimple ↥K) (hAX : A ≤ X)
    (hKs : K ≤ stabSub U) (hAs : A ≤ stabSub U)
    (hAk : ∀ a ∈ A, ∀ w : W, a w * w⁻¹ ∈ U)
    (hKA : ¬ A ≤ Subgroup.centralizer (K : Set (MulAut W))) :
    ∀ x ∈ K, ∀ w : W, x w * w⁻¹ ∈ U := by
  suffices hK : K ≤ szbKer U from fun x hx w => (hK hx).2 w
  obtain ⟨a, haA, haK⟩ := Set.not_subset.mp hKA
  have haKer : a ∈ szbKer U := ⟨hAs haA, hAk a haA⟩
  have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hKq.1
  have hKa : K.map (MulAut.conj a).toMonoidHom ∈ cComp X :=
    CFSG.Quasithin.map_conj_mem_cComp hKc (hAX haA)
  have hKaq : CFSG.IsQuasisimple ↥(K.map (MulAut.conj a).toMonoidHom) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv ((MulAut.conj a).subgroupMap K) hKq
  rcases H13.cComp_eq_or_commutator_eq_bot_of_isQuasisimple hKc hKa hKq hKaq with hKa_eq | hcomm
  ·
    have hconj : ∀ k ∈ K, a * k * a⁻¹ ∈ K := fun k hk => by
      have : a * k * a⁻¹ ∈ K.map (MulAut.conj a).toMonoidHom := ⟨k, hk, rfl⟩
      rwa [← hKa_eq] at this
    have hconj' : ∀ k ∈ K, a⁻¹ * k * a ∈ K := fun k hk => by
      have hk' : k ∈ K.map (MulAut.conj a).toMonoidHom := by rw [← hKa_eq]; exact hk
      obtain ⟨k', hk'K, hk'e⟩ := hk'
      have hk'e' : a * k' * a⁻¹ = k := hk'e
      have : a⁻¹ * k * a = k' := by
        calc a⁻¹ * k * a = a⁻¹ * (a * k' * a⁻¹) * a := by rw [hk'e']
          _ = k' := by group
      rwa [this]
    have hnorm : a ∈ Subgroup.normalizer (K : Set (MulAut W)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro k
      refine ⟨fun hk => hconj k hk, fun hk => ?_⟩
      have h1 := hconj' _ hk
      have e : a⁻¹ * (a * k * a⁻¹) * a = k := by group
      rwa [e] at h1
    set Z : Subgroup (MulAut W) := A ⊓ Subgroup.normalizer (K : Set (MulAut W))
    have haZ : a ∈ Z := Subgroup.mem_inf.mpr ⟨haA, hnorm⟩
    have hNn : ((szbKer U).subgroupOf K).Normal := by
      refine ⟨fun k hk g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hk ⊢
      exact szb_ker_conj (hKs g.2) hk
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hKq hNn with htop | hcent
    · intro k hk
      have : (⟨k, hk⟩ : ↥K) ∈ (szbKer U).subgroupOf K := by rw [htop]; trivial
      exact this
    · exfalso
      have hcen : ∀ c ∈ K, c ∈ szbKer U → ∀ x ∈ K, c * x = x * c := by
        intro c hc hcU x hx
        have hcN : (⟨c, hc⟩ : ↥K) ∈ (szbKer U).subgroupOf K := hcU
        have := Subgroup.mem_center_iff.mp (hcent hcN) ⟨x, hx⟩
        exact (congrArg Subtype.val this).symm
      have hcomm_le : ⁅K, Z⁆ ≤ Subgroup.centralizer (K : Set (MulAut W)) := by
        rw [Subgroup.commutator_le]
        intro x hx z hz
        obtain ⟨hzA, hzN⟩ := Subgroup.mem_inf.mp hz
        have hxK : ⁅x, z⁆ ∈ K := by
          have e : ⁅x, z⁆ = x * (z * x⁻¹ * z⁻¹) := by
            simp only [commutatorElement_def]; group
          rw [e]
          exact K.mul_mem hx ((Subgroup.mem_normalizer_iff.mp hzN x⁻¹).mp (K.inv_mem hx))
        have hzKer : z ∈ szbKer U := ⟨hAs hzA, hAk z hzA⟩
        have hxKer : ⁅x, z⁆ ∈ szbKer U :=
          Subgroup.mul_mem _ (szb_ker_conj (hKs hx) hzKer) (Subgroup.inv_mem _ hzKer)
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        exact (hcen _ hxK hxKer k hk).symm
      have h1 : ⁅⁅K, Z⁆, K⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcomm_le
      have h2 : ⁅⁅Z, K⁆, K⁆ = ⊥ := by rw [Subgroup.commutator_comm Z K]; exact h1
      have h3 : ⁅⁅K, K⁆, Z⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
      rw [hperf] at h3
      apply haK
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro x hx
      have h4 : ⁅x, a⁆ ∈ ⁅K, Z⁆ := Subgroup.commutator_mem_commutator hx haZ
      rw [h3, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h4
      exact h4
  ·
    refine szb_le_of_commutators hperf fun x' hx' x hx => ?_
    have hyK : a * x⁻¹ * a⁻¹ ∈ K.map (MulAut.conj a).toMonoidHom := ⟨x⁻¹, K.inv_mem hx, rfl⟩
    have hxy : x' * (a * x⁻¹ * a⁻¹) = (a * x⁻¹ * a⁻¹) * x' := by
      have hmem := Subgroup.commutator_mem_commutator hx' hyK
      rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem
    have hc : x * (a * x⁻¹ * a⁻¹) ∈ szbKer U := by
      have e : x * (a * x⁻¹ * a⁻¹) = (x * a * x⁻¹) * a⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ (szb_ker_conj (hKs hx) haKer) (Subgroup.inv_mem _ haKer)
    rw [← szb_comm_mul_of_commute hxy]
    exact Subgroup.mul_mem _ (szb_ker_conj (hKs hx') hc) (Subgroup.inv_mem _ hc)

theorem sz_ker_conjClosure {K T : Subgroup (MulAut W)} {U : Subgroup W}
    (hKs : K ≤ stabSub U) (hTs : T ≤ stabSub U)
    (hK : ∀ x ∈ K, ∀ w : W, x w * w⁻¹ ∈ U) :
    ∀ y ∈ conjClosure K T, ∀ w : W, y w * w⁻¹ ∈ U := by
  have hle : conjClosure K T ≤ szbKer U :=
    conjClosure_le fun t ht k hk => szb_ker_conj (hTs ht) ⟨hKs hk, hK k hk⟩
  exact fun y hy => (hle hy).2

end CFSG.Quasithin
