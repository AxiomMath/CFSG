module

public import CFSG.Quasithin.Vol2.Ch11SecBL2UFF2
public import CFSG.Quasithin.Vol2.Ch11SecBL2UOver
public import CFSG.Quasithin.Vol2.Ch11SecBL2F
public import CFSG.Quasithin.Vol2.Ch5Sec1L34ModCoord
public import CFSG.Quasithin.Background.F9Comp

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_isPSU3 {T L I : Subgroup G} {n : ℕ}
    {H K : Subgroup G} {k : ℕ} (hS : L2Setting G T L I n H K k)
    (hU : IsPSU 3 2 k ↥(E2.star (H ⊓ Subgroup.normalizer (L : Set G)) H K)) :
    T ≤ Subgroup.normalizer (K : Set G) := by
  have hcases := hS.cases
  have hk2 := hS.two_le
  have hn1 : E1.nParam H ≠ 1 := hS.nParam.1.ne'
  dsimp only [E2.E22CasesC] at hcases
  rcases hcases with ⟨-, -, -, -, -, h1⟩ | ⟨hTK, -, -⟩
  · exfalso
    rcases h1 with ⟨n', hn'2, htype, -, -⟩ | ⟨_, _, _, _, _, _, h1⟩
    · apply not_a312Out_of_isPSU3 hk2 hU
      rcases htype with hP | hSz
      · exact Or.inr (Or.inl ⟨_, hn'2, hP⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨_, hSz⟩))
    · exact hn1 h1
  · exact hTK

theorem le_normalizer_overgroup (hF : A312Facts)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h39 : A39ForSQTK) {T K Kp Ip : Subgroup G}
    (hfsu : FSU G T Kp Ip) (hKl : quasithinIsLocal T K) (hKKp : K ≤ Kp)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) : T ≤ Subgroup.normalizer (Kp : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKpl : quasithinIsLocal T Kp := hfsu.faithful.1
  set X := Kp ⊔ T with hX
  have hG' := sqtkHyp_quotient_of_pCoreOf_ne_bot hfsu.qtke hfsu.simple hfsu.nonabelian hKpl.2.2.2
  have h312 := a312_refined hF hG' (h36 _ hG') (h37 _ hG') (h39 _ hG')
  have hS : IsSylowTwoOf T X := ⟨le_sup_right, hKpl.1, hKpl.2.2.1⟩
  have hKX : K ≤ X := hKKp.trans le_sup_left
  have hB : K ∈ lFamily T := hKl.2.1
  have hKpc : Kp ∈ cComp X := hKpl.2.1
  have hSbar := isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hS)
    (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) (QuotientGroup.mk'_surjective _)
  obtain ⟨L', -, -, huniq, -⟩ := h312 _ hSbar _ (modO2Image_mem_lFamily hS hKX hB)
  have hKpbar : modO2Image X Kp = L' :=
    huniq _ (modO2Image_mem_cComp hKpc) (Subgroup.map_mono fun x hx => hKKp hx)
  intro t ht
  have htX : t ∈ X := (le_sup_right : T ≤ X) ht
  have hc : conjSub t Kp ∈ cComp X := conjSub_mem_cComp_of_mem hKpc htX
  have hKc : K ≤ conjSub t Kp := by
    intro x hx
    rw [mem_conjSub]
    have := (Subgroup.mem_normalizer_iff.mp (hTK (inv_mem ht)) x).mp hx
    simpa using hKKp this
  have hcbar : modO2Image X (conjSub t Kp) = L' :=
    huniq _ (modO2Image_mem_cComp hc) (Subgroup.map_mono fun x hx => hKc hx)
  have heq : conjSub t Kp = Kp := modO2Image_injOn X hc hKpc (hcbar.trans hKpbar.symm)
  apply H13.mem_normalizer_of_conj_mem
  intro x hx
  have hmem : t * x * t⁻¹ ∈ conjSub t Kp := ⟨x, hx, rfl⟩
  rw [heq] at hmem
  exact hmem

theorem sup_le_normalizer_fsuV {T Kp Ip : Subgroup G} (hfsu : FSU G T Kp Ip)
    (hTKp : T ≤ Subgroup.normalizer (Kp : Set G)) :
    Kp ⊔ T ≤ Subgroup.normalizer (fsuV T Ip : Set G) := by
  have hKpI : Kp ≤ Subgroup.normalizer (Ip : Set G) :=
    (le_conjClosure Kp T).trans hfsu.irrPlus.2.2.1
  have heq : conjClosure Ip (Kp ⊔ T) = conjClosure Ip T := by
    refine le_antisymm (conjClosure_le fun h hh z hz => ?_) (conjClosure_mono le_rfl le_sup_right)
    have hmem : h ∈ (Kp : Set G) * (T : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Kp T hTKp]
      exact hh
    obtain ⟨k, hk, t, ht, rfl⟩ := hmem
    have hk' : t⁻¹ * k * t ∈ Kp := by
      have := (Subgroup.mem_normalizer_iff.mp (hTKp (inv_mem ht)) k).mp hk
      simpa using this
    have hz' : (t⁻¹ * k * t) * z * (t⁻¹ * k * t)⁻¹ ∈ Ip :=
      (Subgroup.mem_normalizer_iff.mp (hKpI hk') z).mp hz
    have := mem_conjClosure ht hz'
    convert this using 1
    group
  show Kp ⊔ T ≤ Subgroup.normalizer (conjClosure Ip T : Set G)
  rw [← heq]
  exact le_normalizer_conjClosure Ip (Kp ⊔ T)

theorem l2Unitary_of
    (hF : A312Facts) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h39 : A39ForSQTK)
    (hM : FactMathieuOrders) (h325 : Stmt3_2_5) (h328 : Stmt3_2_8) (hG2 : FactG2Simple) :
    L2Unitary := by
  intro G _ _ T L I n H K k hS hU Kp Ip hKKp hfsu hcomm hconcl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk2 := hS.two_le
  have hKf : quasithinIsFaithfulLocal T K := l2Faithful_holds G T L I n H K k hS
  have hKl := hKf.1
  have hKpl : quasithinIsLocal T Kp := hfsu.faithful.1
  have hTK := le_normalizer_of_isPSU3 hS hU
  have hTKp := le_normalizer_overgroup hF h36 h37 h39 hfsu hKl hKKp hTK
  rcases hconcl with hFF | h4
  swap
  ·
    have hL0 : fsuL0 T Kp ≤ Kp :=
      conjClosure_le fun t ht x hx => (Subgroup.mem_normalizer_iff.mp (hTKp ht) x).mp hx
    exact absurd h4.1 (not_lt_of_ge hL0)
  have hKH : K ≤ H := by rw [hS.gen]; exact le_sup_left
  set X := H ⊓ Subgroup.normalizer (L : Set G) with hXdef
  set ψ : ↥K →* ↥(E2.star X H K) :=
    ((QuotientGroup.mk' ((kerIn X H).subgroupOf H)).subgroupMap (K.subgroupOf H)).comp
      (Subgroup.subgroupOfEquivOfLe hKH).symm.toMonoidHom with hψ
  have hψs : Function.Surjective ψ :=
    (MonoidHom.subgroupMap_surjective _ _).comp (Subgroup.subgroupOfEquivOfLe hKH).symm.surjective
  have hY : L2BadType k ↥(E2.star X H K) := Or.inr (Or.inl hU)
  have : IsSimpleGroup ↥(E2.star X H K) := hY.isSimpleGroup hk2
  have : Group.IsPerfect ↥K := A36A.isPerfect_of_mem_cComp hKl.2.1
  have hYab := nonabelian_of_perfect_surjective ψ hψs
  have hG' := sqtkHyp_quotient_of_pCoreOf_ne_bot hfsu.qtke hfsu.simple hfsu.nonabelian hKpl.2.2.2
  have h312 := a312_refined hF hG' (h36 _ hG') (h37 _ hG') (h39 _ hG')
  rcases overgroup_iso_or_a312Out hM hk2 hY hKl hKpl hKKp hS.quasisimple ψ hψs h312 with
    he | hout
  swap
  · exact not_a312Out_of_isPSU3 hk2 hU hout
  obtain ⟨e⟩ := he
  obtain ⟨ψ', hψ'⟩ := exists_surjective_of_modO2_equiv hYab e ψ hψs
  have : Group.IsPerfect ↥Kp := A36A.isPerfect_of_mem_cComp hKpl.2.1
  have : (CFSG.pCore 2 ↥Kp).Normal := CFSG.pCore_normal
  have hQ : CFSG.Open.IsQuasisimple (↥Kp ⧸ CFSG.pCore 2 ↥Kp) :=
    ⟨hfsu.quasisimple.1.commutator_eq_top, hfsu.quasisimple.2.1⟩
  exact u3_false_of_concl701FF h325 h328 hG2 hfsu hTKp (sup_le_normalizer_fsuV hfsu hTKp) hYab
    CFSG.pCore_isPGroup hQ ψ' hψ' hk2 hU hFF

end CFSG.Quasithin.Vol2.Ch11.SecB
