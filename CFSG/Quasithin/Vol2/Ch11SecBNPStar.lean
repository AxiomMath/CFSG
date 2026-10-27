module

public import CFSG.Quasithin.Vol2.Ch11SecBNPComp

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

variable {Γ : Type} [Group Γ]

theorem pow_mem_of_mem_sup_normal {N T : Subgroup Γ} [N.Normal] (hT : IsPGroup 2 T) :
    ∀ y ∈ N ⊔ T, ∃ e : ℕ, y ^ 2 ^ e ∈ N := by
  intro y hy
  obtain ⟨n, hn, t, ht, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hy
  obtain ⟨e, he⟩ := hT ⟨t, ht⟩
  have hte : t ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
  refine ⟨e, ?_⟩
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
    (QuotientGroup.eq_one_iff n).mpr hn, one_mul, ← QuotientGroup.mk_pow, hte,
    QuotientGroup.mk_one]

theorem normal_iSup_conj (K : Subgroup Γ) :
    (⨆ h : Γ, K.map (MulAut.conj h).toMonoidHom).Normal := by
  constructor
  intro n hn g
  have hle : (⨆ h : Γ, K.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom ≤
      ⨆ h : Γ, K.map (MulAut.conj h).toMonoidHom := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun h => ?_
    have hcomp : (MulAut.conj g).toMonoidHom.comp (MulAut.conj h).toMonoidHom =
        (MulAut.conj (g * h)).toMonoidHom := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [Subgroup.map_map, hcomp]
    exact le_iSup (fun h => K.map (MulAut.conj h).toMonoidHom) (g * h)
  exact hle (Subgroup.mem_map_of_mem _ hn)

theorem secAll_of_simple_subnormal [Finite Γ] {P : GrpPred} (hP : IsoInv P)
    {K T O Y : Subgroup Γ} (hKs : IsSimpleGroup ↥K) (hKab : ∃ a b : ↥K, a * b ≠ b * a)
    (hKsn : K.IsSubnormal) (hPK : P ↥K) (hT : IsPGroup 2 T) (hKT : K ⊔ T = ⊤)
    (hOn : O.Normal) (hKO : K ≤ O) (hOY : O ≤ Y) : SecAll ↥Y P := by
  set S : Γ → Subgroup Γ := fun h => K.map (MulAut.conj h).toMonoidHom with hSdef
  have hSY : ∀ h, S h ≤ Y := fun h => by
    rintro _ ⟨x, hx, rfl⟩
    exact hOY (hOn.conj_mem x (hKO hx) h)
  let eS : ∀ h, ↥K ≃* ↥(S h) := fun h =>
    K.equivMapOfInjective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective
  set S' : Γ → Subgroup ↥Y := fun h => (S h).subgroupOf Y with hS'def
  let e' : ∀ h, ↥(S' h) ≃* ↥K := fun h =>
    (Subgroup.subgroupOfEquivOfLe (hSY h)).trans (eS h).symm
  refine secAll_of_components hP (Set.range S') ?_ ?_
  · rintro _ ⟨h, rfl⟩
    refine ⟨(e' h).isSimpleGroup, ?_, ?_, hP _ _ (e' h) hPK⟩
    · obtain ⟨a, b, hab⟩ := hKab
      refine ⟨(e' h).symm a, (e' h).symm b, fun hc => hab ((e' h).symm.injective ?_)⟩
      rw [map_mul, map_mul, hc]
    · exact (hKsn.map (MulAut.conj h).surjective).subgroupOf
  · intro g
    set N := ⨆ h : Γ, S h with hN
    have hNn : N.Normal := normal_iSup_conj K
    have hKN : K ≤ N := fun x hx => Subgroup.mem_iSup_of_mem 1 ⟨x, hx, by simp⟩
    have hgN : (g : Γ) ∈ N ⊔ T := by
      have : (g : Γ) ∈ K ⊔ T := by rw [hKT]; trivial
      exact sup_le_sup_right hKN T this
    obtain ⟨e, he⟩ := pow_mem_of_mem_sup_normal hT _ hgN
    refine ⟨e, ?_⟩
    have hmap : (sSup (Set.range S')).map Y.subtype = N := by
      rw [sSup_range, Subgroup.map_iSup]
      refine iSup_congr fun h => ?_
      rw [hS'def, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hSY h)]
    have hmem : ((g ^ 2 ^ e : ↥Y) : Γ) ∈ (sSup (Set.range S')).map Y.subtype := by
      rw [hmap]
      simpa using he
    obtain ⟨y, hy, hyg⟩ := hmem
    have : y = g ^ 2 ^ e := Subtype.ext hyg
    rw [← this]
    exact hy

end CFSG.Quasithin.Vol2.Ch11.SecB
