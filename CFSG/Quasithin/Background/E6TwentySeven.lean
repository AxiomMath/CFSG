module

public import CFSG.Quasithin.Background.E6TwentySix

public section

namespace CFSG.Quasithin
namespace E6

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem le_sup_normalizer_of_isSylowTwoOf {B N K : Subgroup G} (hB : IsSylowTwoOf B N)
    (hNK : N ≤ K) (hK : K ≤ Subgroup.normalizer (N : Set G)) :
    K ≤ N ⊔ (K ⊓ Subgroup.normalizer (B : Set G)) := by
  intro k hk
  have hkN : k ∈ Subgroup.normalizer (N : Set G) := hK hk
  have hB' : IsSylowTwoOf (cjSub k B) N := by
    refine ⟨cjSub_le hkN hB.1, ?_, ?_⟩
    · exact hB.2.1.map (MulAut.conj k).toMonoidHom
    · have h1 : (cjSub k B).relIndex N = B.relIndex N := by
        have e : cjSub k N = N := Subgroup.eq_of_le_of_card_ge (cjSub_le hkN le_rfl)
          (by rw [card_cjSub])
        have h2 : (cjSub k B).relIndex (cjSub k N) = B.relIndex N :=
          Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj k).toMonoidHom) B N
            (MulAut.conj k).injective
        rw [e] at h2
        exact h2
      change ¬ 2 ∣ (cjSub k B).relIndex N
      rw [h1]
      exact hB.2.2
  obtain ⟨n, hn, hnk⟩ := B6.isSylowTwoOf_exists_conj hB hB'
  have key : ∀ x, k⁻¹ * x * k ∈ B ↔ n⁻¹ * x * n ∈ B := fun x => by
    have := congrArg (fun X : Subgroup G => x ∈ X) hnk
    simpa only [mem_cjSub, B6.mem_conjSub, eq_iff_iff] using this
  have hm : n⁻¹ * k ∈ Subgroup.normalizer (B : Set G) := by
    refine E5.mem_normalizer_of_cjSub_eq ?_
    ext y
    rw [mem_cjSub]
    have e1 : (n⁻¹ * k)⁻¹ * y * (n⁻¹ * k) = k⁻¹ * (n * y * n⁻¹) * k := by group
    have e2 : n⁻¹ * (n * y * n⁻¹) * n = y := by group
    rw [e1, key, e2]
  have : k = n * (n⁻¹ * k) := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hn)
    (Subgroup.mem_sup_right ⟨K.mul_mem (K.inv_mem (hNK hn)) hk, hm⟩)

theorem thompsonJk_le_of_isSylowTwoOf {j : ℕ} {S X : Subgroup G} (hS : IsSylowTwoOf S X) :
    H13.thompsonJk j S ≤ H13.thompsonJk j X := by
  refine iSup₂_le fun A hA => E5.le_thompsonJk (hA.1.trans hS.1) hA.2.1 fun B hBX hB => ?_
  obtain ⟨x, -, hxB⟩ := exists_conj_le_of_isSylowTwoOf hS hBX (B2F.isPGroup_of_isElemAbelian hB)
  have := hA.2.2 _ hxB (isElemAbelian_cjSub hB)
  rwa [card_cjSub] at this

theorem normalizer_thompsonJ_le {Q S M : Subgroup G}
    (hM : IsUniqueM (Subgroup.normalizer (Q : Set G)) M) (hJQ : thompsonJ S ≤ Q) (hQS : Q ≤ S)
    (hS2 : IsPGroup 2 S) (hJ1 : thompsonJ S ≠ ⊥) :
    Subgroup.normalizer (thompsonJ S : Set G) ≤ M := by
  have hJeq : thompsonJ S = thompsonJ Q := thompsonJ_eq_of_le hJQ hQS
  have hNQ : Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (thompsonJ S : Set G) := by
    intro g hg
    rw [hJeq]
    exact E5.mem_normalizer_of_cjSub_eq (cjSub_thompsonJ hg)
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge
    (⟨thompsonJ S, hJ1, hS2.to_le (thompsonJ_le_self S), rfl⟩ :
      IsTwoLocal (Subgroup.normalizer (thompsonJ S : Set G)))
  have hM'eq : M' = M := hM.2 M' ⟨hM', hNQ.trans hle⟩
  rw [← hM'eq]
  exact hle

theorem isSylowTwoOf_of_normalizer_le {M K S : Subgroup G} (hS : IsSylowTwoOf S (M ⊓ K))
    (hSK : S ≤ K) (_hSM : S ≤ M) (hNS : Subgroup.normalizer (S : Set G) ≤ M) :
    IsSylowTwoOf S K := by
  have hS2 : IsPGroup 2 S := hS.2.1
  rw [A4.isSylowTwoOf_iff_maximal]
  refine ⟨hSK, hS2, fun P hPK hP2 hSP => ?_⟩
  by_contra hPS
  have hlt : S.subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hPS
    intro x hx
    have : (⟨x, hx⟩ : ↥P) ∈ S.subgroupOf P := htop ▸ Subgroup.mem_top _
    exact this
  have hP2' : IsPGroup 2 ↥P := hP2
  have : Group.IsNilpotent ↥P := hP2'.isNilpotent
  have hgrow := Group.normalizerCondition_of_isNilpotent (G := ↥P) _ hlt
  obtain ⟨y, hyN, hyS⟩ := IsConcreteLE.exists_of_lt hgrow
  have hyS' : (y : G) ∉ S := hyS
  have hyNS : (y : G) ∈ Subgroup.normalizer (S : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have h1 : (⟨z, hSP hz⟩ : ↥P) ∈ S.subgroupOf P := hz
      exact (Subgroup.mem_normalizer_iff.1 hyN _).1 h1
    · intro hz
      have hzP : z ∈ P := by
        have : (y : G)⁻¹ * ((y : G) * z * (y : G)⁻¹) * (y : G) = z := by group
        rw [← this]
        exact P.mul_mem (P.mul_mem (P.inv_mem y.2) (hSP hz)) y.2
      have h1 : (⟨z, hzP⟩ : ↥P) ∈ S.subgroupOf P := by
        refine (Subgroup.mem_normalizer_iff.1 hyN _).2 ?_
        exact hz
      exact h1
  have hyM : (y : G) ∈ M ⊓ K := ⟨hNS hyNS, hPK y.2⟩
  have hSy : S ⊔ Subgroup.zpowers (y : G) ≤ M ⊓ K :=
    sup_le hS.1 (Subgroup.zpowers_le.2 hyM)
  have hSy2 : IsPGroup 2 ↥(S ⊔ Subgroup.zpowers (y : G)) :=
    hP2.to_le (sup_le hSP (Subgroup.zpowers_le.2 y.2))
  have := (A4.isSylowTwoOf_iff_maximal.1 hS).2.2 _ hSy hSy2 le_sup_left
  exact hyS' (this (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))

theorem e6_27_of_parabolics {T M V U : Subgroup G} (h : HypE61 T M V) (hUV : U ≤ V)
    {j : ℕ} (hj : 0 < j) (hr : (j : ℕ∞) < E3.rParam V)
    (hS : IsSylowTwoOf (T ⊓ Subgroup.centralizer (U : Set G))
      (M ⊓ Subgroup.centralizer (U : Set G)))
    (h2 : H13.thompsonJk j (M ⊓ Subgroup.centralizer (U : Set G)) ≤
      M ⊓ Subgroup.centralizer (V : Set G))
    (hpar : ∀ H ∈ uFamHat (twoPrimeResidual (Subgroup.centralizer (U : Set G)))
        (T ⊓ Subgroup.centralizer (U : Set G)), (j : ℕ∞) < E1.nParam H → H ≤ M) :
    Subgroup.centralizer (U : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := T ⊓ Subgroup.centralizer (U : Set G) with hSdef
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  set K := Subgroup.centralizer (U : Set G) with hKdef
  have hS2 : IsPGroup 2 S := h.sylow.1.to_le inf_le_left
  have hCVU : Subgroup.centralizer (V : Set G) ≤ K := Subgroup.centralizer_le hUV
  have hQS : Q ≤ S := inf_le_inf_left _ hCVU
  have hJS : H13.thompsonJk j S ≤ S ⊓ Subgroup.centralizer (V : Set G) :=
    le_inf (E5.thompsonJk_le j S)
      ((thompsonJk_le_of_isSylowTwoOf hS).trans (h2.trans inf_le_right))
  have hVQ : V ≤ Q := h.le_inf_centralizer
  have hJ1 : thompsonJ S ≠ ⊥ :=
    thompsonJ_ne_bot (hVQ.trans hQS) h.isElemAbelian h.ne_bot
  have hNS : Subgroup.normalizer (S : Set G) ≤ M := by
    have hJQ : thompsonJ S ≤ Q :=
      (thompsonJ_le_thompsonJk j S).trans (hJS.trans (inf_le_inf_right _ inf_le_left))
    have hNJ := normalizer_thompsonJ_le h.isUniqueM_normalizer_Q hJQ hQS hS2 hJ1
    exact fun g hg => hNJ (E5.mem_normalizer_of_cjSub_eq (cjSub_thompsonJ hg))
  have hSK : IsSylowTwoOf S K :=
    isSylowTwoOf_of_normalizer_le hS inf_le_right (h.inM.2.trans' inf_le_left) hNS
  set K₁ := twoPrimeResidual K with hK₁def
  have hK₁ : conjClosure S K = K₁ := conjClosure_eq_twoPrimeResidual hSK
  have hK₁K : K₁ ≤ K := by
    rw [← hK₁]
    exact conjClosure_le fun k hk s hs => K.mul_mem (K.mul_mem hk hs.2) (K.inv_mem hk)
  have hSK₁ : S ≤ K₁ := hK₁ ▸ le_conjClosure S K
  have hSsyl : IsSylowTwoOf S K₁ := A4.isSylowTwoOf_mono hSK hSK₁ hK₁K
  have hKN : K ≤ Subgroup.normalizer (K₁ : Set G) := hK₁ ▸ le_normalizer_conjClosure S K
  have hfrat : K ≤ K₁ ⊔ (K ⊓ Subgroup.normalizer (S : Set G)) :=
    le_sup_normalizer_of_isSylowTwoOf hSsyl hK₁K hKN
  have hK₁M : K₁ ≤ M := by
    rcases eq_or_lt_of_le hSK₁ with heq | hlt
    · exact heq ▸ (inf_le_left.trans h.inM.2)
    · have hcl : conjClosure S K₁ = K₁ := by
        refine le_antisymm (conjClosure_le fun k hk s hs =>
          K₁.mul_mem (K₁.mul_mem hk (hSK₁ hs)) (K₁.inv_mem hk)) ?_
        calc K₁ = conjClosure S K := hK₁.symm
          _ ≤ conjClosure S K₁ := conjClosure_le fun k hk s hs => by
            have hk' := hfrat hk
            rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left K₁ _
              (inf_le_left.trans hKN)] at hk'
            obtain ⟨a, ha, b, hb, rfl⟩ := hk'
            have hbs : b * s * b⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 hb.2 s).1 hs
            have e : a * b * s * (a * b)⁻¹ = a * (b * s * b⁻¹) * a⁻¹ := by group
            rw [e]
            exact mem_conjClosure ha hbs
      have hgen := uHat_eq_of_conjClosure_eq hSK₁ (by rw [hcl]; exact hlt) hcl
      rw [← hgen]
      refine iSup₂_le fun P hP => ?_
      have hPK₁ : P ≤ K₁ := hP.1.1
      have hSP : S ≤ P := hP.1.2.1.le
      have hSPsyl : IsSylowTwoOf S P := A4.isSylowTwoOf_mono hSsyl hSP hPK₁
      by_cases hn : (j : ℕ∞) < E1.nParam P
      · exact hpar P hP hn
      · exact (e6_26 h.sylow.1 h.ne_bot h.isElemAbelian h.le h.normalizer_le
          h.isUniqueM_normalizer_Q hj (not_lt.1 hn) hSPsyl hQS inf_le_left hr hJS).1
  calc K ≤ K₁ ⊔ (K ⊓ Subgroup.normalizer (S : Set G)) := hfrat
    _ ≤ M := sup_le hK₁M (inf_le_right.trans hNS)

end E6
end CFSG.Quasithin
