module

public import CFSG.Quasithin.EmptyFaithful.S152Y14

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S152Y

section Frattini

variable {A : Type} [Group A] [Finite A]

omit [Finite A] in
theorem isSylowTwoOf_map_conj {S N : Subgroup A} (hS : IsSylowTwoOf S N) {x : A}
    (hx : x ∈ Subgroup.normalizer (N : Set A)) :
    IsSylowTwoOf (S.map (MulAut.conj x).toMonoidHom) N := by
  have hmapN : N.map (MulAut.conj x).toMonoidHom = N := by
    ext y
    constructor
    · rintro ⟨n, hn, rfl⟩
      have := (Subgroup.mem_normalizer_iff.mp hx n).mp hn
      simpa using this
    · intro hy
      refine ⟨x⁻¹ * y * x, ?_, by simp [mul_assoc]⟩
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (N : Set A)).inv_mem hx) y).mp hy
      simpa using this
  refine ⟨?_, hS.2.1.map _, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    rw [← hmapN]
    exact ⟨s, hS.1 hs, rfl⟩
  · have h1 := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj x).toMonoidHom) S N
      (MulAut.conj x).injective
    rw [hmapN] at h1
    have h2 : (S.map (MulAut.conj x).toMonoidHom).relIndex N = S.relIndex N := h1
    show ¬ 2 ∣ (S.map (MulAut.conj x).toMonoidHom).relIndex N
    rw [h2]
    exact hS.2.2

theorem exists_mem_normalizer_of_sylow {S N X : Subgroup A} (hS : IsSylowTwoOf S N)
    (hXN : X ≤ Subgroup.normalizer (N : Set A)) {x : A} (hx : x ∈ X) :
    ∃ n ∈ N, n⁻¹ * x ∈ Subgroup.normalizer (S : Set A) := by
  have hS' := isSylowTwoOf_map_conj hS (hXN hx)
  obtain ⟨g, hgN, hg⟩ := A4.exists_conj_of_isSylowTwoOf hS' hS
  refine ⟨g⁻¹, N.inv_mem hgN, ?_⟩
  rw [inv_inv]
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have key : ∀ w : A, w ∈ S ↔ x⁻¹ * (g⁻¹ * w * g) * x ∈ S := by
    intro w
    rw [hg w, Subgroup.mem_map]
    constructor
    · rintro ⟨s, hs, hsw⟩
      have : x⁻¹ * (g⁻¹ * w * g) * x = s := by
        have h2 : x * s * x⁻¹ = g⁻¹ * w * g := hsw
        rw [← h2]; group
      rw [this]; exact hs
    · intro h2
      refine ⟨x⁻¹ * (g⁻¹ * w * g) * x, h2, ?_⟩
      show x * (x⁻¹ * (g⁻¹ * w * g) * x) * x⁻¹ = g⁻¹ * w * g
      group
  have h3 := key (g * x * z * (g * x)⁻¹)
  have h4 : x⁻¹ * (g⁻¹ * (g * x * z * (g * x)⁻¹) * g) * x = z := by group
  rw [h4] at h3
  exact h3.symm

end Frattini

section Main

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

theorem mem_normalizer_inf_centralizer (h : Data T Mc M) {J : Subgroup G} (hJM : J ≤ M)
    {n : G} (hnM : n ∈ M)
    (hn : conjAct (V154 T Mc M) ⟨n, h.hMV hnM⟩ ∈
      Subgroup.normalizer (autOn J (V154 T Mc M) : Set (MulAut (V154 T Mc M)))) :
    n ∈ Subgroup.normalizer
      ((V154 T Mc M ⊓ Subgroup.centralizer (J : Set G) : Subgroup G) : Set G) := by
  have fwd : ∀ n' : G, ∀ hn'M : n' ∈ M,
      conjAct (V154 T Mc M) ⟨n', h.hMV hn'M⟩ ∈
        Subgroup.normalizer (autOn J (V154 T Mc M) : Set (MulAut (V154 T Mc M))) →
      ∀ v ∈ V154 T Mc M ⊓ Subgroup.centralizer (J : Set G),
        n' * v * n'⁻¹ ∈ V154 T Mc M ⊓ Subgroup.centralizer (J : Set G) := by
    intro n' hn'M hn' v hv
    have hn'N := h.hMV hn'M
    refine ⟨(Subgroup.mem_normalizer_iff.mp hn'N v).mp hv.1, ?_⟩
    show n' * v * n'⁻¹ ∈ Subgroup.centralizer (J : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have hjM : j ∈ M := hJM hj
    have hjN : j ∈ Subgroup.normalizer (V154 T Mc M : Set G) := h.hMV hjM
    have hj'M : n'⁻¹ * j * n' ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hn'M) hjM) hn'M
    have hj'N : n'⁻¹ * j * n' ∈ Subgroup.normalizer (V154 T Mc M : Set G) := h.hMV hj'M
    have hconj : conjAct (V154 T Mc M) ⟨n'⁻¹ * j * n', hj'N⟩ ∈ autOn J (V154 T Mc M) := by
      have e : (⟨n'⁻¹ * j * n', hj'N⟩ : Subgroup.normalizer (V154 T Mc M : Set G)) =
          (⟨n', hn'N⟩ : Subgroup.normalizer (V154 T Mc M : Set G))⁻¹ * ⟨j, hjN⟩ * ⟨n', hn'N⟩ := rfl
      rw [e, map_mul, map_mul, map_inv]
      have hinv := (Subgroup.normalizer
        (autOn J (V154 T Mc M) : Set (MulAut (V154 T Mc M)))).inv_mem hn'
      have := (Subgroup.mem_normalizer_iff.mp hinv (conjAct (V154 T Mc M) ⟨j, hjN⟩)).mp
        (mem_autOn_of_mem hjN hj)
      simpa using this
    obtain ⟨j'', hj''N, hj''J, hj''⟩ := mem_autOn_iff_exists.mp hconj
    have hc : j''⁻¹ * (n'⁻¹ * j * n') ∈ Subgroup.centralizer (V154 T Mc M : Set G) :=
      (conjAct_eq_iff hj''N hj'N).mp hj''
    have h1 : (n'⁻¹ * j * n') * v = v * (n'⁻¹ * j * n') := by
      set c := j''⁻¹ * (n'⁻¹ * j * n') with hcdef
      have e1 : n'⁻¹ * j * n' = j'' * c := by rw [hcdef]; group
      have hcv : v * c = c * v := Subgroup.mem_centralizer_iff.mp hc v hv.1
      have hjv : j'' * v = v * j'' := Subgroup.mem_centralizer_iff.mp hv.2 j'' hj''J
      rw [e1]
      calc j'' * c * v = j'' * (c * v) := by group
        _ = j'' * (v * c) := by rw [← hcv]
        _ = (j'' * v) * c := by group
        _ = (v * j'') * c := by rw [hjv]
        _ = v * (j'' * c) := by group
    calc j * (n' * v * n'⁻¹) = n' * ((n'⁻¹ * j * n') * v) * n'⁻¹ := by group
      _ = n' * (v * (n'⁻¹ * j * n')) * n'⁻¹ := by rw [h1]
      _ = n' * v * n'⁻¹ * j := by group
  rw [Subgroup.mem_normalizer_iff]
  intro v
  constructor
  · exact fun hv => fwd n hnM hn v hv
  · intro hv
    have hnM' : n⁻¹ ∈ M := M.inv_mem hnM
    have hn' : conjAct (V154 T Mc M) ⟨n⁻¹, h.hMV hnM'⟩ ∈
        Subgroup.normalizer (autOn J (V154 T Mc M) : Set (MulAut (V154 T Mc M))) := by
      have e : (⟨n⁻¹, h.hMV hnM'⟩ : Subgroup.normalizer (V154 T Mc M : Set G)) =
          (⟨n, h.hMV hnM⟩ : Subgroup.normalizer (V154 T Mc M : Set G))⁻¹ := rfl
      rw [e, map_inv]
      exact (Subgroup.normalizer
        (autOn J (V154 T Mc M) : Set (MulAut (V154 T Mc M)))).inv_mem hn
    have h6 := fwd n⁻¹ hnM' hn' _ hv
    have e : n⁻¹ * (n * v * n⁻¹) * n⁻¹⁻¹ = v := by group
    rw [e] at h6
    exact h6

theorem frattini_main (h : Data T Mc M) (h1513 : Lemma15113Concl T Mc M)
    (h1514 : Lemma15114Concl T Mc M) :
    ∀ x ∈ M, ∃ y ∈ m0Of T Mc M, ∃ n ∈ M ⊓ Mc, x = y * n := by
  intro x hx
  have hxN : x ∈ Subgroup.normalizer (V154 T Mc M : Set G) := h.hMV hx
  by_cases hThree : Case1517Three M (V154 T Mc M) (mBar0 T Mc M)
  · refine ⟨x, ?_, 1, (M ⊓ Mc).one_mem, (mul_one x).symm⟩
    have hA : autOn M (V154 T Mc M) = mBar0 T Mc M := hThree.2.1
    refine mem_preOn.mpr ⟨hx, hxN, ?_⟩
    rw [← hA]
    exact mem_autOn_of_mem hxN hx
  · rcases h1513.four with ⟨hJ, -⟩ | ⟨hTh, -⟩
    · have hsyl0 : IsSylowTwoOf (autOn T (V154 T Mc M) ⊓ mBar0 T Mc M) (mBar0 T Mc M) :=
        A4.isSylowTwoOf_inf_normal (isSylowTwoOf_Tb h) (mBar0_le T Mc M) (mBar0_normalizer T Mc M)
      obtain ⟨nb, hnb, hnbx⟩ := exists_mem_normalizer_of_sylow hsyl0
        (mBar0_normalizer T Mc M) (mem_autOn_of_mem hxN hx)
      have hnb' : nb ∈ autOn (m0Of T Mc M) (V154 T Mc M) := by
        rw [autOn_m0Of]; exact hnb
      obtain ⟨y, hyN, hyM0, hy⟩ := mem_autOn_iff_exists.mp hnb'
      have hyM : y ∈ M := m0Of_le T Mc M hyM0
      have hnM : y⁻¹ * x ∈ M := M.mul_mem (M.inv_mem hyM) hx
      have hnN : y⁻¹ * x ∈ Subgroup.normalizer (V154 T Mc M : Set G) := h.hMV hnM
      have hact : conjAct (V154 T Mc M) ⟨y⁻¹ * x, hnN⟩ =
          nb⁻¹ * conjAct (V154 T Mc M) ⟨x, hxN⟩ := by
        have e : (⟨y⁻¹ * x, hnN⟩ : Subgroup.normalizer (V154 T Mc M : Set G)) =
            (⟨y, hyN⟩ : Subgroup.normalizer (V154 T Mc M : Set G))⁻¹ * ⟨x, hxN⟩ := rfl
        rw [e, map_mul, map_inv, hy]
      have hJT : thompsonJi T 1 ≤ T := iSup₂_le fun _ hA => hA.1
      have hJM : thompsonJi T 1 ≤ M := hJT.trans h.T_le
      have hnorm := mem_normalizer_inf_centralizer h hJM hnM
        (by rw [hact, hJ]; exact hnbx)
      have hMc : y⁻¹ * x ∈ Mc := (h1514.two fun hB => hThree hB.1).2 hnorm
      exact ⟨y, hyM0, y⁻¹ * x, ⟨hnM, hMc⟩, (mul_inv_cancel_left y x).symm⟩
    · exact absurd hTh hThree

theorem frattini_field (h : Data T Mc M) (h1513 : Lemma15113Concl T Mc M)
    (h1514 : Lemma15114Concl T Mc M) :
    (M : Set G) = ((M ⊓ Mc : Subgroup G) : Set G) * (oTwoUpper (m0Of T Mc M) : Set G) := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨y, hy, n, hn, hxy⟩ := frattini_main h h1513 h1514 x⁻¹ (M.inv_mem hx)
    have hsyl : IsSylowTwoOf (T ⊓ m0Of T Mc M) (m0Of T Mc M) :=
      A4.isSylowTwoOf_inf_normal (isSylowTwoOf_of_le151 h.qtfe.sylow h.T_le) (m0Of_le T Mc M)
        h.le_normalizer_m0Of
    have hM0 : m0Of T Mc M = oTwoUpper (m0Of T Mc M) ⊔ (T ⊓ m0Of T Mc M) :=
      eq_oTwoUpper_sup_of_isSylowTwoOf hsyl
    have hSN : T ⊓ m0Of T Mc M ≤ Subgroup.normalizer (oTwoUpper (m0Of T Mc M) : Set G) :=
      inf_le_right.trans (le_normalizer_oTwoUpper _)
    have hmul := Subgroup.coe_mul_of_right_le_normalizer_left (oTwoUpper (m0Of T Mc M))
      (T ⊓ m0Of T Mc M) hSN
    have hy' : y ∈ (oTwoUpper (m0Of T Mc M) : Set G) * ((T ⊓ m0Of T Mc M : Subgroup G) : Set G) := by
      rw [← hmul, ← hM0]; exact hy
    obtain ⟨y₀, hy₀, s, hs, rfl⟩ := hy'
    have hsn : s * n ∈ M ⊓ Mc := (M ⊓ Mc).mul_mem ⟨h.T_le hs.1, h.T_le_Mc hs.1⟩ hn
    refine ⟨(s * n)⁻¹, (M ⊓ Mc).inv_mem hsn, y₀⁻¹, (oTwoUpper _).inv_mem hy₀, ?_⟩
    have h5 : x⁻¹ = y₀ * (s * n) := by rw [hxy]; group
    calc (s * n)⁻¹ * y₀⁻¹ = (y₀ * (s * n))⁻¹ := by group
      _ = x := by rw [← h5, inv_inv]
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact M.mul_mem ha.1 (y0Of_le T Mc M hb)

end Main


end S152Y

end CFSG.Quasithin
