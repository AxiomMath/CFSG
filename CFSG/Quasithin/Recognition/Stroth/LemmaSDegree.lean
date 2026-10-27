module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.SylowIndex

public section

namespace CFSG.Quasithin.Stroth

open scoped Pointwise

universe u

theorem relIndex_le_card_right_of_sup_eq {G : Type u} [Group G] [Finite G]
    {U T B : Subgroup G} (hB : B = U ⊔ T)
    (hT : T ≤ Subgroup.normalizer (U : Set G)) :
    U.relIndex B ≤ Nat.card T := by
  classical
  let φ : T → B ⧸ U.subgroupOf B := fun t =>
    QuotientGroup.mk (⟨(t : G), by rw [hB]; exact Subgroup.mem_sup_right t.2⟩ : B)
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
    have hb : (b : G) ∈ (U ⊔ T : Subgroup G) := by rw [← hB]; exact b.2
    have hTU : ((T ⊔ U : Subgroup G) : Set G) = (T : Set G) * (U : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right T U hT
    have hb' : (b : G) ∈ (T : Set G) * (U : Set G) := by
      rw [← hTU]
      simpa [sup_comm] using hb
    obtain ⟨t, ht, u, hu, htu⟩ := hb'
    have htB : t ∈ B := by rw [hB]; exact Subgroup.mem_sup_right ht
    refine ⟨⟨t, ht⟩, ?_⟩
    change QuotientGroup.mk (⟨t, htB⟩ : B) = QuotientGroup.mk b
    rw [QuotientGroup.eq]
    rw [Subgroup.mem_subgroupOf]
    change t⁻¹ * (b : G) ∈ U
    rw [← htu]
    simpa using hu
  have hle := Nat.card_le_card_of_surjective φ hsurj
  rw [Subgroup.relIndex, Subgroup.index_eq_card]
  exact hle

theorem injOn_mul_quotient_of_regular {G : Type u} {Ω : Type*} [Group G] [MulAction G Ω]
    (B U : Subgroup G) (α : Ω) (hB : B = MulAction.stabilizer G α) (hU : U ≤ B)
    (hreg : ∀ a b : Ω, a ≠ α → b ≠ α → ∃! u : U, u • a = b)
    {y : G} (hy : y ∉ B) :
    Set.InjOn (fun s : G => (QuotientGroup.mk (s * y) : G ⧸ B)) (U : Set G) := by
  intro s hs t ht hst
  have hmem : (s * y)⁻¹ * (t * y) ∈ B := QuotientGroup.eq.mp hst
  have hfix : ((⟨s⁻¹ * t, U.mul_mem (U.inv_mem hs) ht⟩ : U) : G) • (y • α) = y • α := by
    have h := hmem
    rw [hB, MulAction.mem_stabilizer_iff] at h
    have hgroup : (s * y)⁻¹ * (t * y) = y⁻¹ * (s⁻¹ * t) * y := by group
    rw [hgroup] at h
    have h' : ((s⁻¹ * t) * y) • α = y • α := by
      have := congrArg (fun z => y • z) h
      simpa [mul_smul, mul_assoc] using this
    change (s⁻¹ * t) • (y • α) = y • α
    rw [← mul_smul]
    exact h'
  have hyα : y • α ≠ α := by
    intro hya
    apply hy
    rw [hB, MulAction.mem_stabilizer_iff]
    exact hya
  have huniq := (hreg (y • α) (y • α) hyα hyα).unique hfix
    (one_smul U (y • α))
  have hst' : s⁻¹ * t = 1 := congrArg Subtype.val huniq
  exact inv_mul_eq_one.mp hst'

theorem le_B_or_eq_top_of_bruhat {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    {B U T : Subgroup G} {n : G}
    (hB : B = U ⊔ T) (hTnorm : T ≤ Subgroup.normalizer (U : Set G))
    (hnT : ∀ t ∈ T, n⁻¹ * t * n ∈ T) (hnsq : n * n = 1) (hUbot : U ≠ ⊥)
    (hbruhat : ∀ g : G, g ∈ B ∨ ∃ b₁ ∈ B, ∃ b₂ ∈ B, g = b₁ * n * b₂) :
    ∀ M : Subgroup G, U ≤ M → M ≤ B ∨ M = ⊤ := by
  intro M hUM
  by_cases hMB : M ≤ B
  · exact Or.inl hMB
  · right
    let Y : Subgroup G := U ⊔ U.map (MulAut.conj n).toMonoidHom
    have hYdef : Y = U ⊔ U.map (MulAut.conj n).toMonoidHom := rfl
    have hYeq : Y = Subgroup.closure ((U : Set G) ∪
        (U.map (MulAut.conj n).toMonoidHom : Set G)) := by
      rw [hYdef, Subgroup.sup_eq_closure]
    have hUY : U ≤ Y := le_sup_left
    have hUnY : U.map (MulAut.conj n).toMonoidHom ≤ Y := le_sup_right
    obtain ⟨m, hmM, hmB⟩ := Set.not_subset.mp hMB
    rcases hbruhat m with hm | ⟨b₁, hb₁, b₂, hb₂, hm⟩
    · exact absurd hm hmB
    ·
      have hb₁' : (b₁ : G) ∈ (U : Set G) * (T : Set G) := by
        have hUT : ((U ⊔ T : Subgroup G) : Set G) = (U : Set G) * (T : Set G) :=
          Subgroup.coe_mul_of_right_le_normalizer_left U T hTnorm
        rw [← hUT, ← hB]
        exact hb₁
      obtain ⟨u₁, hu₁, t₁, ht₁, hb₁eq⟩ := hb₁'
      have hb₂' : (b₂ : G) ∈ (T : Set G) * (U : Set G) := by
        have hTU : ((T ⊔ U : Subgroup G) : Set G) = (T : Set G) * (U : Set G) :=
          Subgroup.coe_mul_of_left_le_normalizer_right T U hTnorm
        rw [← hTU]
        have : b₂ ∈ U ⊔ T := by rw [← hB]; exact hb₂
        simpa [sup_comm] using this
      obtain ⟨t₂, ht₂, u₂, hu₂, hb₂eq⟩ := hb₂'
      have hmeq : m = u₁ * t₁ * n * t₂ * u₂ := by
        rw [hm, ← hb₁eq, ← hb₂eq]
        group
      have hu₂M : u₂ ∈ M := hUM hu₂
      have hmulM : u₁ * t₁ * n * t₂ ∈ M := by
        have := M.mul_mem hmM (M.inv_mem hu₂M)
        simpa [hmeq, mul_assoc] using this
      have hu₁M : u₁ ∈ M := hUM hu₁
      have ht₁nt₂M : t₁ * n * t₂ ∈ M := by
        have := M.mul_mem (M.inv_mem hu₁M) hmulM
        simpa [mul_assoc] using this
      have hnt : n * (n⁻¹ * t₁ * n * t₂) ∈ M := by
        have htn : t₁ * n * t₂ = n * (n⁻¹ * t₁ * n) * t₂ := by group
        rw [htn] at ht₁nt₂M
        simpa [mul_assoc] using ht₁nt₂M
      let t₃ : T := ⟨n⁻¹ * t₁ * n * t₂, T.mul_mem (hnT t₁ ht₁) ht₂⟩
      have hnt₃ : n * (t₃ : G) ∈ M := by simpa [t₃] using hnt
      have hUnM : U.map (MulAut.conj n).toMonoidHom ≤ M := by
        intro x hx
        rcases hx with ⟨u, hu, rfl⟩
        change n * u * n⁻¹ ∈ M
        have hu' : (t₃ : G)⁻¹ * u * (t₃ : G) ∈ U := by
          simpa using (Subgroup.mem_normalizer_iff.mp
            (hTnorm (T.inv_mem t₃.2)) u).mp hu
        have hx : n * u * n⁻¹ = (n * (t₃ : G)) * ((t₃ : G)⁻¹ * u * (t₃ : G)) *
            (n * (t₃ : G))⁻¹ := by group
        rw [hx]
        exact M.mul_mem (M.mul_mem hnt₃ (hUM hu')) (M.inv_mem hnt₃)
      have hYleM : Y ≤ M := sup_le hUM hUnM
      have hUnN : T ≤ Subgroup.normalizer
          (U.map (MulAut.conj n).toMonoidHom : Set G) := by
        intro t ht
        rw [Subgroup.mem_normalizer_iff_map_conj_eq]
        have ht' : n⁻¹ * t * n ∈ T := hnT t ht
        have hUm : U.map (MulAut.conj (n⁻¹ * t * n)).toMonoidHom = U :=
          Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTnorm ht')
        calc
          (U.map (MulAut.conj n).toMonoidHom).map (MulAut.conj t).toMonoidHom =
              U.map ((MulAut.conj t).toMonoidHom.comp
                (MulAut.conj n).toMonoidHom) := by
            rw [Subgroup.map_map]
          _ = U.map (MulAut.conj (t * n)).toMonoidHom := by
            congr 1
            ext u
            simp [MulAut.conj_apply, mul_assoc]
          _ = U.map (MulAut.conj (n * (n⁻¹ * t * n))).toMonoidHom := by group
          _ = (U.map (MulAut.conj (n⁻¹ * t * n)).toMonoidHom).map
                (MulAut.conj n).toMonoidHom := by
            rw [Subgroup.map_map]
            congr 1
            ext u
            simp [MulAut.conj_apply, mul_assoc]
          _ = U.map (MulAut.conj n).toMonoidHom := by rw [hUm]
      have hTnormY : T ≤ Subgroup.normalizer (Y : Set G) := by
        rw [hYdef]
        exact (le_inf hTnorm hUnN).trans
          (Subgroup.inf_normalizer_le_normalizer_sup U _)
      have hBnormY : B ≤ Subgroup.normalizer (Y : Set G) := by
        rw [hB]
        refine sup_le ?_ hTnormY
        intro u hu
        exact Subgroup.le_normalizer (hUY hu)
      have hnY : n ∈ Subgroup.normalizer (Y : Set G) := by
        rw [Subgroup.mem_normalizer_iff_map_conj_eq]
        rw [hYdef]
        have hcomp : (U.map (MulAut.conj n).toMonoidHom).map
            (MulAut.conj n).toMonoidHom = U := by
          rw [Subgroup.map_map]
          have hninv : n⁻¹ = n := inv_eq_of_mul_eq_one_right hnsq
          have hcomp' : (MulAut.conj n).toMonoidHom.comp
              (MulAut.conj n).toMonoidHom = MonoidHom.id G := by
            ext u
            rw [MonoidHom.comp_apply, MonoidHom.id_apply]
            change n * (n * u * n⁻¹) * n⁻¹ = u
            rw [hninv]
            calc
              n * (n * u * n) * n = (n * n) * u * (n * n) := by group
              _ = u := by rw [hnsq]; simp
          rw [hcomp', Subgroup.map_id]
        rw [Subgroup.map_sup]
        change U.map (MulAut.conj n).toMonoidHom ⊔
            (U.map (MulAut.conj n).toMonoidHom).map (MulAut.conj n).toMonoidHom =
          U ⊔ U.map (MulAut.conj n).toMonoidHom
        rw [hcomp, sup_comm]
      have hYnormal : Y.Normal := by
        rw [← Subgroup.normalizer_eq_top_iff]
        apply top_le_iff.mp
        intro g _
        rcases hbruhat g with hg | ⟨b₁, hb₁, b₂, hb₂, rfl⟩
        · exact hBnormY hg
        · exact (Subgroup.normalizer (Y : Set G)).mul_mem
            ((Subgroup.normalizer (Y : Set G)).mul_mem (hBnormY hb₁) hnY) (hBnormY hb₂)
      have hYtop : Y = ⊤ := by
        haveI : Y.Normal := hYnormal
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Y with h | h
        · exfalso
          apply hUbot
          rw [eq_bot_iff]
          intro u hu
          have : u ∈ Y := hUY hu
          rw [h] at this
          exact this
        · exact h
      exact top_le_iff.mp (hYtop ▸ hYleM)

structure RankOneData (N : Type u) [Group N] (U B : Subgroup N) : Prop where
  isPGroup : IsPGroup 2 U
  ne_bot : U ≠ ⊥
  isSylow : ∃ S : Sylow 2 N, (S : Subgroup N) = U
  U_le_B : U ≤ B
  overgroup_le_B : ∀ M : Subgroup N, U ≤ M → M < ⊤ → M ≤ B
  index_B : B.index = 1 + Nat.card U
  relIndex_lt : U.relIndex B < Nat.card U

theorem RankOneData.map {N N' : Type u} [Group N] [Group N'] [Finite N] [Finite N']
    (e : N ≃* N') {U B : Subgroup N} (h : RankOneData N U B) :
    RankOneData N' (U.map e.toMonoidHom) (B.map e.toMonoidHom) where
  isPGroup := h.isPGroup.map e.toMonoidHom
  ne_bot := by
    intro hbot
    apply h.ne_bot
    exact (Subgroup.map_eq_bot_iff_of_injective U (by simpa using e.injective)).mp hbot
  isSylow := by
    obtain ⟨S, hS⟩ := h.isSylow
    refine ⟨S.mapSurjective (f := e.toMonoidHom) (by simpa using e.surjective), ?_⟩
    simpa [Sylow.coe_mapSurjective, hS]
  U_le_B := Subgroup.map_mono h.U_le_B
  overgroup_le_B := by
    intro M' hUM' hM'
    let M : Subgroup N := M'.comap e.toMonoidHom
    have hUM : U ≤ M := by
      rw [← Subgroup.map_le_iff_le_comap]
      exact hUM'
    have hMtop : M < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      apply hM'.ne
      have hmap_top : M.map e.toMonoidHom = ⊤ := by rw [htop]; simp
      rw [Subgroup.map_comap_eq_self_of_surjective (by simpa using e.surjective) M'] at hmap_top
      exact hmap_top
    have hMB : M ≤ B := h.overgroup_le_B M hUM hMtop
    have hmap : M.map e.toMonoidHom ≤ B.map e.toMonoidHom := Subgroup.map_mono hMB
    rwa [Subgroup.map_comap_eq_self_of_surjective (by simpa using e.surjective) M'] at hmap
  index_B := by
    have h1 : (B.map e.toMonoidHom).index = B.index := by
      simpa [MulEquiv.coe_toMonoidHom] using Subgroup.index_map_equiv B e
    have h2 : Nat.card (U.map e.toMonoidHom) = Nat.card U :=
      Subgroup.card_map_of_injective e.injective
    rw [h1, h2, h.index_B]
  relIndex_lt := by
    have h1 : (U.map e.toMonoidHom).relIndex (B.map e.toMonoidHom) = U.relIndex B := by
      simpa [MulEquiv.coe_toMonoidHom] using
        Subgroup.relIndex_map_map_of_injective U B e.injective
    have h2 : Nat.card (U.map e.toMonoidHom) = Nat.card U :=
      Subgroup.card_map_of_injective e.injective
    rw [h1, h2]
    exact h.relIndex_lt

theorem card_eq_one_add_of_rankOneData {Y : Type u} {Ω : Type*} [Group Y] [Finite Y]
    [Fintype Ω] [MulAction Y Ω] [FaithfulSMul Y Ω] (N : Subgroup Y) [N.Normal]
    (hNbot : N ≠ ⊥) (h2 : MulAction.IsMultiplyPretransitive Y Ω 2)
    {c : ℕ} (hdeg : ∃ e : ℕ, 1 ≤ e ∧ Fintype.card Ω = 1 + 2 ^ e)
    (hdata : ∃ U B : Subgroup N, RankOneData N U B ∧ Nat.card U = c) :
    Fintype.card Ω = 1 + c := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, he1, hcardΩ⟩ := hdeg
  have hfixed : MulAction.fixedPoints N Ω ≠ ⊤ := by
    intro htop
    obtain ⟨n, hn1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hNbot
    have hfixall : ∀ x : Ω, n • x = x := fun x => by
      have hx : x ∈ MulAction.fixedPoints N Ω := by rw [htop]; exact Set.mem_univ x
      exact hx n
    have h1 : n = 1 :=
      FaithfulSMul.eq_of_smul_eq_smul (fun x => by rw [hfixall x, one_smul])
    exact hn1 h1
  haveI : MulAction.IsPreprimitive Y Ω :=
    MulAction.isPreprimitive_of_is_two_pretransitive h2
  have hNtrans : MulAction.IsPretransitive N Ω :=
    MulAction.IsQuasiPreprimitive.isPretransitive_of_normal (N := N) hfixed
  have hpos : 0 < Fintype.card Ω := by rw [hcardΩ]; positivity
  let ω : Ω := (Fintype.card_pos_iff.mp hpos).some
  let M : Subgroup N := MulAction.stabilizer N ω
  have hMindex : M.index = Fintype.card Ω := by
    rw [MulAction.index_stabilizer_of_transitive N ω, Nat.card_eq_fintype_card]
  have hMtop : M < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hfixed
    change MulAction.fixedPoints N Ω = Set.univ
    rw [Set.eq_univ_iff_forall]
    intro x
    rw [MulAction.mem_fixedPoints]
    intro m
    obtain ⟨n, rfl⟩ := MulAction.exists_smul_eq N ω x
    have hnfix : n • ω = ω := by
      have : n ∈ M := htop ▸ Subgroup.mem_top n
      simpa [M] using this
    calc
      m • (n • ω) = (m * n) • ω := (mul_smul m n ω).symm
      _ = ω := by
        have hmn : m * n ∈ M := htop ▸ Subgroup.mem_top (m * n)
        simpa [M] using hmn
      _ = n • ω := hnfix.symm
  have hodd : Odd M.index := by
    rw [hMindex, hcardΩ]
    have he0 : e ≠ 0 := by omega
    obtain ⟨k, hk⟩ := Nat.even_pow.mpr ⟨even_two, he0⟩
    exact ⟨k, by omega⟩
  have hnotdvd : ¬ 2 ∣ M.index := fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  obtain ⟨U, B, hdataU, hUcard⟩ := hdata
  obtain ⟨x, hx⟩ :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.exists_conj_le_of_not_dvd_index
      Nat.prime_two M hnotdvd U hdataU.isPGroup
  let e1 : N ≃* N := MulAut.conj x
  let U' : Subgroup N := U.map e1.toMonoidHom
  let B' : Subgroup N := B.map e1.toMonoidHom
  have hU'data : RankOneData N U' B' := hdataU.map e1
  have hU'le : U' ≤ M := by
    intro y hy
    rcases hy with ⟨u, hu, rfl⟩
    exact hx u hu
  have hU'card : Nat.card U' = c := by
    rw [Subgroup.card_map_of_injective e1.injective, hUcard]
  have hMleB : M ≤ B' :=
    hU'data.overgroup_le_B M hU'le (lt_top_iff_ne_top.mpr hMtop.ne)
  haveI : U'.IsFiniteRelIndex B' := Subgroup.isFiniteRelIndex_of_finiteIndex
  have hm_lt : M.relIndex B' < c := by
    have hle : M.relIndex B' ≤ U'.relIndex B' :=
      Subgroup.relIndex_le_of_le_left hU'le (Subgroup.relIndex_ne_zero (H := U') (K := B'))
    calc
      M.relIndex B' ≤ U'.relIndex B' := hle
      _ < c := by simpa [hU'card] using hU'data.relIndex_lt
  haveI : M.IsFiniteRelIndex B' := Subgroup.isFiniteRelIndex_of_finiteIndex
  have hm_pos : 1 ≤ M.relIndex B' := by
    rw [Nat.one_le_iff_ne_zero]
    exact Subgroup.relIndex_ne_zero (H := M) (K := B')
  have hindex_mul : M.index = (1 + c) * M.relIndex B' := by
    rw [← Subgroup.relIndex_mul_index hMleB, hU'data.index_B, hU'card]
    ring
  have h_eq : 1 + 2 ^ e = (1 + c) * M.relIndex B' := by
    rw [← hcardΩ, ← hMindex, hindex_mul]
  by_cases hm1 : M.relIndex B' = 1
  · have h' : 1 + 2 ^ e = 1 + c := by simpa [hm1] using h_eq
    rw [hcardΩ]
    exact h'
  · exfalso
    have hm_gt : 1 < M.relIndex B' := lt_of_le_of_ne hm_pos (Ne.symm hm1)
    have hm2 : 2 ≤ M.relIndex B' := hm_gt
    have hc_lt : c < 2 ^ e := by
      have h1 : (1 + c) * 2 ≤ (1 + c) * M.relIndex B' :=
        Nat.mul_le_mul_left (1 + c) hm2
      rw [← h_eq] at h1
      omega
    obtain ⟨k, hk⟩ := hdataU.isPGroup.exists_card_eq
    have hc_eq : c = 2 ^ k := by rw [← hUcard, hk]
    have hklt : k < e := by
      rw [hc_eq] at hc_lt
      exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hc_lt
    have hc_dvd : c ∣ 2 ^ e := by
      rw [hc_eq]
      exact pow_dvd_pow 2 (le_of_lt hklt)
    have h_eq2 : 2 ^ e = c * M.relIndex B' + (M.relIndex B' - 1) := by
      have h1 : 1 + 2 ^ e = c * M.relIndex B' + M.relIndex B' := by
        rw [h_eq]; ring
      omega
    have hc_dvd_m1 : c ∣ M.relIndex B' - 1 := by
      have hc_dvd_prod : c ∣ c * M.relIndex B' := dvd_mul_right c _
      have hsub : 2 ^ e - c * M.relIndex B' = M.relIndex B' - 1 := by omega
      simpa [hsub] using Nat.dvd_sub hc_dvd hc_dvd_prod
    have hc_pos : 0 < c := by rw [← hU'card]; exact Nat.card_pos
    have hc_le : c ≤ M.relIndex B' - 1 := Nat.le_of_dvd (by omega) hc_dvd_m1
    omega

end CFSG.Quasithin.Stroth
