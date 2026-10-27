module

public import CFSG.Quasithin.EmptyFaithful.S151S9UDef
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.S151S9U

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem perfectCore_top_le_of_index_two_pow {X : Type*} [Group X] [Finite X] (A : Subgroup X)
    [A.Normal] (hA : ∃ k : ℕ, A.index = 2 ^ k) : perfectCore (⊤ : Subgroup X) ≤ A := by
  obtain ⟨k, hk⟩ := hA
  have hp : IsPGroup 2 (X ⧸ A) := IsPGroup.of_card hk
  have : Group.IsNilpotent (X ⧸ A) := hp.isNilpotent
  have h1 : perfectCore (⊤ : Subgroup (X ⧸ A)) = ⊥ :=
    (isSolvable_iff_perfectCore_eq_bot _).mp inferInstance
  have h2 := map_perfectCore (QuotientGroup.mk' A) (⊤ : Subgroup X)
  rw [Subgroup.map_top, MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective A),
    h1] at h2
  exact (QuotientGroup.ker_mk' A) ▸ (Subgroup.map_eq_bot_iff _).mp h2

theorem sup_eq_top_of_index_two_pow {X : Type*} [Group X] {A B : Subgroup X}
    (hA : ∃ k : ℕ, A.index = 2 ^ k) (hB : ¬ 2 ∣ B.index) : A ⊔ B = ⊤ := by
  obtain ⟨k, hk⟩ := hA
  have h1 : (A ⊔ B).index ∣ 2 ^ k := hk ▸ Subgroup.index_dvd_of_le le_sup_left
  have h2 : (A ⊔ B).index ∣ B.index := Subgroup.index_dvd_of_le le_sup_right
  have hcop : Nat.Coprime (2 ^ k) B.index :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hB)
  exact Subgroup.index_eq_one.mp
    (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2)

theorem normal_perfectCore_top (X : Type*) [Group X] : (perfectCore (⊤ : Subgroup X)).Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
  have h := normalizer_le_normalizer_perfectCore (⊤ : Subgroup X)
  rwa [Subgroup.normalizer_eq_top (⊤ : Subgroup X)] at h

theorem perfectCore_eq_alternatingGroup {m : ℕ} (hm : 5 ≤ m)
    {M : Subgroup (Equiv.Perm (Fin m))} (hM : alternatingGroup (Fin m) ≤ M) :
    perfectCore M = alternatingGroup (Fin m) := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  refine le_antisymm ?_
    (le_perfectCore_of_perfect hM (commutator_alternatingGroup_eq_self (by simpa using hm)))
  exact (perfectCore_mono le_top).trans (perfectCore_top_le_of_index_two_pow _ ⟨1, by simp⟩)

theorem perfectCore_top_map_eq_alternatingGroup {N : Type*} [Group N] [Finite N] {m : ℕ}
    (hm : 5 ≤ m) (φ : N →* Equiv.Perm (Fin m)) (halt : alternatingGroup (Fin m) ≤ φ.range) :
    (perfectCore (⊤ : Subgroup N)).map φ = alternatingGroup (Fin m) := by
  rw [map_perfectCore, Subgroup.map_top]
  exact perfectCore_eq_alternatingGroup hm halt

theorem perfectCore_top_index_two_pow {N : Type*} [Group N] [Finite N] {m : ℕ} (hm : 5 ≤ m)
    (φ : N →* Equiv.Perm (Fin m)) (hker : IsPGroup 2 ↥φ.ker)
    (halt : alternatingGroup (Fin m) ≤ φ.range) :
    ∃ b : ℕ, (perfectCore (⊤ : Subgroup N)).index = 2 ^ b := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have := normal_perfectCore_top N
  have himage := perfectCore_top_map_eq_alternatingGroup hm φ halt
  set K := perfectCore (⊤ : Subgroup N) with hK
  have hR : (K ⊔ φ.ker).index ∣ 2 := by
    have h1 := Subgroup.dvd_index_map (K ⊔ φ.ker) (f := φ) le_sup_right
    have h2 : (K ⊔ φ.ker).map φ = alternatingGroup (Fin m) := by
      rw [Subgroup.map_sup, himage, Subgroup.map_ker_self, sup_bot_eq]
    rwa [h2, alternatingGroup.index_eq_two] at h1
  have hKR : K.relIndex (K ⊔ φ.ker) ∣ Nat.card φ.ker := by
    rw [Subgroup.relIndex_sup_left]
    exact Subgroup.relIndex_dvd_card _ _
  obtain ⟨c, hc⟩ := IsPGroup.iff_card.mp hker
  obtain ⟨b₁, -, hb₁⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hc ▸ hKR)
  obtain ⟨b₂, -, hb₂⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show (K ⊔ φ.ker).index ∣ 2 ^ 1 by simpa using hR)
  exact ⟨b₁ + b₂, by rw [← Subgroup.relIndex_mul_index (le_sup_left : K ≤ K ⊔ φ.ker), hb₁, hb₂,
    pow_add]⟩

theorem map_mem_cComp_of_injective {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Injective f) {L X : Subgroup G} (hL : L ∈ cComp X) :
    L.map f ∈ cComp (X.map f) := by
  obtain ⟨hne, hperf, hsub, hmin⟩ := hL
  refine ⟨?_, ?_, A3.subnormal_map f hsub, ?_⟩
  · intro h
    exact hne (Subgroup.map_injective hf (h.trans (Subgroup.map_bot f).symm))
  · rw [← Subgroup.map_commutator, hperf]
  · intro K hlt hKne hKperf hKsub
    have hKle : K ≤ f.range := hlt.le.trans (Subgroup.map_le_range f L)
    have hmc : (K.comap f).map f = K := Subgroup.map_comap_eq_self hKle
    have hLc : (L.map f).comap f = L := Subgroup.comap_map_eq_self_of_injective hf L
    have hlt' : K.comap f < L := by
      refine lt_of_le_of_ne (hLc ▸ Subgroup.comap_mono hlt.le) fun h => hlt.ne ?_
      rw [← hmc, h]
    refine hmin (K.comap f) hlt' ?_ ?_ ?_
    · intro h
      exact hKne (by rw [← hmc, h, Subgroup.map_bot])
    · refine Subgroup.map_injective hf ?_
      rw [Subgroup.map_commutator, hmc, hKperf]
    · simpa [Subgroup.comap_map_eq_self_of_injective hf X] using A3.subnormal_comap f hKsub

theorem le_ker_of_normal_ne_top {K S : Type*} [Group K] [Group S] [IsSimpleGroup S]
    [Group.IsPerfect K] (ψ : K →* S) (hψ : Function.Surjective ψ)
    (hsolv : Group.IsSolvable ↥ψ.ker) (T : Subgroup K) [T.Normal] (hT : T ≠ ⊤) :
    T ≤ ψ.ker := by
  have : (T.map ψ).Normal := Subgroup.Normal.map inferInstance ψ hψ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (T.map ψ) with h | h
  · exact (Subgroup.map_eq_bot_iff _).mp h
  · exfalso
    have hsup : T ⊔ ψ.ker = ⊤ := by rw [← Subgroup.comap_map_eq, h, Subgroup.comap_top]
    have hle := perfectCore_le_of_sup_solvable (A := T) (B := ψ.ker) (Y := ⊤) le_top
      Subgroup.normal_subgroupOf hsup.symm hsolv
    rw [perfectCore_eq_self_of_perfect (Subgroup.commutator_eq_self (H := (⊤ : Subgroup K)))] at hle
    exact hT (top_le_iff.mp hle)

theorem mem_cComp_self_of_simple_quotient {G : Type*} [Group G] [Finite G] {K : Subgroup G}
    {S : Type*} [Group S] [IsSimpleGroup S] (ψ : ↥K →* S) (hψ : Function.Surjective ψ)
    (hne : K ≠ ⊥) (hperf : ⁅K, K⁆ = K) (hsolv : Group.IsSolvable ↥ψ.ker) : K ∈ cComp K := by
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hperf
  refine ⟨hne, hperf, IsSubnormal.refl K, fun K' hlt hK'ne hK'perf hsub => ?_⟩
  obtain ⟨P, hPK, hPn, hK'P⟩ := A3.subnormal_exists_normal_of_lt hsub hlt
  have : (P.subgroupOf K).Normal := hPn
  have hT : P.subgroupOf K ≠ ⊤ := fun h => hPK.not_ge (Subgroup.subgroupOf_eq_top.mp h)
  have hTker : P.subgroupOf K ≤ ψ.ker := le_ker_of_normal_ne_top ψ hψ hsolv _ hT
  have hTsolv : Group.IsSolvable ↥(P.subgroupOf K) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hTker)
      (Subgroup.inclusion_injective hTker)
  have hPsolv : Group.IsSolvable ↥P :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hPK.le).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPK.le).surjective
  have hK'solv : Group.IsSolvable ↥K' :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hK'P)
      (Subgroup.inclusion_injective hK'P)
  have h0 := (isSolvable_iff_perfectCore_eq_bot K').mp hK'solv
  rw [perfectCore_eq_self_of_perfect hK'perf] at h0
  exact hK'ne h0

theorem perfectCore_top_mem_cComp {N : Type*} [Group N] [Finite N] {m : ℕ} (hm : 5 ≤ m)
    (φ : N →* Equiv.Perm (Fin m)) (hker : IsPGroup 2 ↥φ.ker)
    (halt : alternatingGroup (Fin m) ≤ φ.range) :
    perfectCore (⊤ : Subgroup N) ≠ ⊥ ∧
      perfectCore (⊤ : Subgroup N) ∈ cComp (perfectCore (⊤ : Subgroup N)) := by
  have hsimple : IsSimpleGroup ↥(alternatingGroup (Fin m)) :=
    alternatingGroup.isSimpleGroup (by simpa using hm)
  have himage := perfectCore_top_map_eq_alternatingGroup hm φ halt
  have hKne : perfectCore (⊤ : Subgroup N) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.map_bot] at himage
    exact (Subgroup.nontrivial_iff_ne_bot _).mp hsimple.toNontrivial himage.symm
  have hmem : ∀ x : ↥(perfectCore (⊤ : Subgroup N)),
      (φ.comp (perfectCore (⊤ : Subgroup N)).subtype) x ∈ alternatingGroup (Fin m) := fun x => by
    rw [← himage]
    exact Subgroup.mem_map_of_mem φ x.2
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : ↥(perfectCore (⊤ : Subgroup N)) →* ↥(alternatingGroup (Fin m)),
      ψ = (φ.comp (perfectCore (⊤ : Subgroup N)).subtype).codRestrict _ hmem := ⟨_, rfl⟩
  have hψ : Function.Surjective ψ := by
    rintro ⟨a, ha⟩
    rw [← himage] at ha
    obtain ⟨x, hx, rfl⟩ := ha
    exact ⟨⟨x, hx⟩, by rw [hψdef]; rfl⟩
  have hsolv : Group.IsSolvable ↥ψ.ker := by
    have hp : IsPGroup 2 ↥ψ.ker := by
      rw [hψdef, MonoidHom.ker_codRestrict, ← MonoidHom.comap_ker]
      exact hker.comap_of_injective _ (perfectCore (⊤ : Subgroup N)).subtype_injective
    have : Group.IsNilpotent ↥ψ.ker := hp.isNilpotent
    infer_instance
  exact ⟨hKne, mem_cComp_self_of_simple_quotient ψ hψ hKne (perfectCore_perfect _) hsolv⟩

theorem perfCore_of_actionData {Q : Type} [Group Q] [Finite Q] {P Y : Subgroup Q}
    (hP : IsSylowTwoOf P Y) (h : ActionData Y) : PerfCore P Y := by
  obtain ⟨N, m, φ, hNn, ⟨k, hk⟩, hm, hker, halt⟩ := h
  have hKN : perfectCore (⊤ : Subgroup ↥Y) ≤ N :=
    perfectCore_top_le_of_index_two_pow N ⟨k, hk⟩
  have hK'K : (perfectCore (⊤ : Subgroup ↥N)).map N.subtype = perfectCore (⊤ : Subgroup ↥Y) := by
    rw [map_perfectCore, Subgroup.map_top, Subgroup.range_subtype]
    exact le_antisymm (perfectCore_mono le_top)
      (le_perfectCore_of_perfect hKN (perfectCore_perfect _))
  have hKQ : perfectCore Y = (perfectCore (⊤ : Subgroup ↥Y)).map Y.subtype := by
    rw [map_perfectCore, Subgroup.map_top, Subgroup.range_subtype]
  have hinj : Function.Injective (Y.subtype.comp N.subtype) :=
    Y.subtype_injective.comp N.subtype_injective
  have hfQ : perfectCore Y = (perfectCore (⊤ : Subgroup ↥N)).map (Y.subtype.comp N.subtype) := by
    rw [hKQ, ← hK'K, Subgroup.map_map]
  obtain ⟨hK'ne, hK'c⟩ := perfectCore_top_mem_cComp hm φ hker halt
  refine ⟨?_, ?_, ?_⟩
  · rw [hfQ]
    intro h0
    exact hK'ne (Subgroup.map_injective hinj (h0.trans (Subgroup.map_bot _).symm))
  · rw [hfQ]
    exact map_mem_cComp_of_injective _ hinj hK'c
  · obtain ⟨b, hb⟩ := perfectCore_top_index_two_pow hm φ hker halt
    have hKidx : ∃ j : ℕ, (perfectCore (⊤ : Subgroup ↥Y)).index = 2 ^ j := by
      refine ⟨b + k, ?_⟩
      rw [← hK'K, Subgroup.index_map_subtype, hb, hk, pow_add]
    have htop := sup_eq_top_of_index_two_pow hKidx hP.2.2
    have h1 := congrArg (Subgroup.map Y.subtype) htop
    rwa [Subgroup.map_sup, ← hKQ, Subgroup.map_subgroupOf_eq_of_le hP.1, Subgroup.map_top,
      Subgroup.range_subtype] at h1

end CFSG.Quasithin.S151S9U
