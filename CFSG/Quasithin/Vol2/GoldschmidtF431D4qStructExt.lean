module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4ExtMap

public section

namespace CFSG.Quasithin.H13.F431.D4q.Struct

open CFSG.Quasithin CFSG.QuasithinUnique

structure KIso {D D' : Type} [Group D] [Group D'] (A : LieAmalgamExt D)
    (A' : LieAmalgamExt D') where
  ψ : ↥A.K ≃* ↥A'.K
  mem1 : ∀ k, ψ k ∈ A'.Mb1 ↔ k ∈ A.Mb1
  mem2 : ∀ k, ψ k ∈ A'.Mb2 ↔ k ∈ A.Mb2

structure LocIso {D D' : Type} [Group D] [Group D'] {G : Type} [Group G] {M1 M2 : Subgroup G}
    (E : LieExt D M1 M2) (E' : LieExt D' M1 M2) extends
    KIso E.toLieAmalgamExt E'.toLieAmalgamExt where
  amalg : ∀ k, amalgamMap E'.b1 E'.b2 (ψ k) = amalgamMap E.b1 E.b2 k

def LocIso.trans {D D' D'' : Type} [Group D] [Group D'] [Group D''] {G : Type} [Group G]
    {M1 M2 : Subgroup G} {E : LieExt D M1 M2} {E' : LieExt D' M1 M2} {E'' : LieExt D'' M1 M2}
    (L : LocIso E E') (L' : LocIso E' E'') : LocIso E E'' where
  ψ := L.ψ.trans L'.ψ
  mem1 k := by
    simp only [MulEquiv.trans_apply]
    exact (L'.mem1 (L.ψ k)).trans (L.mem1 k)
  mem2 k := by
    simp only [MulEquiv.trans_apply]
    exact (L'.mem2 (L.ψ k)).trans (L.mem2 k)
  amalg k := by
    simp only [MulEquiv.trans_apply]
    exact (L'.amalg (L.ψ k)).trans (L.amalg k)

end CFSG.Quasithin.H13.F431.D4q.Struct

namespace CFSG.Quasithin.H13.F431.LieExt

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431.D4q.Struct

variable {D D' : Type} [Group D] [Group D'] {G : Type} [Group G] {M1 M2 : Subgroup G}
  (E : LieExt D M1 M2) (e : D ≃* D') (Mbar' : Subgroup (MulAut D'))
  (hM : Mbar' = E.Mbar.map (MulAut.congr e).toMonoidHom)

theorem congrOf_N1 :
    (E.congrOf e Mbar' hM).N1 = E.N1.map (MulAut.congr e).toMonoidHom := by
  show Mbar' ⊓ autStab (E.P1.map e.toMonoidHom) = _
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.congr e).injective, autStab_map, hM]

theorem congrOf_N2 :
    (E.congrOf e Mbar' hM).N2 = E.N2.map (MulAut.congr e).toMonoidHom := by
  show Mbar' ⊓ autStab (E.P2.map e.toMonoidHom) = _
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.congr e).injective, autStab_map, hM]

theorem congrOf_K : (E.congrOf e Mbar' hM).K = E.K.map (MulAut.congr e).toMonoidHom := by
  unfold LieAmalgamExt.K
  rw [E.congrOf_N1 e Mbar' hM, E.congrOf_N2 e Mbar' hM, Subgroup.map_sup]

@[expose] noncomputable def congrOfK : ↥E.K ≃* ↥(E.congrOf e Mbar' hM).K :=
  let eK : ↥E.K ≃* ↥(E.K.map (MulAut.congr e).toMonoidHom) := (MulAut.congr e).subgroupMap E.K
  eK.trans (MulEquiv.subgroupCongr (E.congrOf_K e Mbar' hM).symm)

theorem congrOfK_val (k : ↥E.K) :
    ((E.congrOfK e Mbar' hM k : ↥(E.congrOf e Mbar' hM).K) : MulAut D') =
      MulAut.congr e (k : MulAut D) := rfl

theorem congrOf_phi1_val (x : ↥M1) :
    (((E.congrOf e Mbar' hM).phi1 x : ↥(E.congrOf e Mbar' hM).N1) : MulAut D') =
      MulAut.congr e ((E.phi1 x : ↥E.N1) : MulAut D) := rfl

theorem congrOf_phi2_val (x : ↥M2) :
    (((E.congrOf e Mbar' hM).phi2 x : ↥(E.congrOf e Mbar' hM).N2) : MulAut D') =
      MulAut.congr e ((E.phi2 x : ↥E.N2) : MulAut D) := rfl

theorem congrOfK_mem1 (k : ↥E.K) :
    E.congrOfK e Mbar' hM k ∈ (E.congrOf e Mbar' hM).Mb1 ↔ k ∈ E.Mb1 := by
  rw [LieAmalgamExt.Mb1, LieAmalgamExt.Mb1, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
    congrOfK_val, E.congrOf_N1 e Mbar' hM]
  exact Subgroup.mem_map_iff_mem (f := (MulAut.congr e).toMonoidHom) (MulAut.congr e).injective

theorem congrOfK_mem2 (k : ↥E.K) :
    E.congrOfK e Mbar' hM k ∈ (E.congrOf e Mbar' hM).Mb2 ↔ k ∈ E.Mb2 := by
  rw [LieAmalgamExt.Mb2, LieAmalgamExt.Mb2, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
    congrOfK_val, E.congrOf_N2 e Mbar' hM]
  exact Subgroup.mem_map_iff_mem (f := (MulAut.congr e).toMonoidHom) (MulAut.congr e).injective

theorem congrOfK_b1 (k : ↥E.K) (hk : k ∈ E.Mb1)
    (hk' : E.congrOfK e Mbar' hM k ∈ (E.congrOf e Mbar' hM).Mb1) :
    (E.congrOf e Mbar' hM).b1 ⟨E.congrOfK e Mbar' hM k, hk'⟩ = E.b1 ⟨k, hk⟩ := by
  rw [LieExt.b1_apply, LieExt.b1_apply]
  congr 1
  apply (E.congrOf e Mbar' hM).phi1.injective
  rw [MulEquiv.apply_symm_apply]
  exact Subtype.ext (by rw [congrOf_phi1_val]; simp [congrOfK_val])

theorem congrOfK_b2 (k : ↥E.K) (hk : k ∈ E.Mb2)
    (hk' : E.congrOfK e Mbar' hM k ∈ (E.congrOf e Mbar' hM).Mb2) :
    (E.congrOf e Mbar' hM).b2 ⟨E.congrOfK e Mbar' hM k, hk'⟩ = E.b2 ⟨k, hk⟩ := by
  rw [LieExt.b2_apply, LieExt.b2_apply]
  congr 1
  apply (E.congrOf e Mbar' hM).phi2.injective
  rw [MulEquiv.apply_symm_apply]
  exact Subtype.ext (by rw [congrOf_phi2_val]; simp [congrOfK_val])

theorem amalgamMap_congrOfK (k : ↥E.K) :
    amalgamMap (E.congrOf e Mbar' hM).b1 (E.congrOf e Mbar' hM).b2 (E.congrOfK e Mbar' hM k) =
      amalgamMap E.b1 E.b2 k := by
  by_cases h1 : k ∈ E.Mb1
  · have h1' := (E.congrOfK_mem1 e Mbar' hM k).2 h1
    rw [amalgamMap_of_mem₁ _ _ h1', amalgamMap_of_mem₁ _ _ h1, E.congrOfK_b1 e Mbar' hM k h1 h1']
  · have h1' : E.congrOfK e Mbar' hM k ∉ (E.congrOf e Mbar' hM).Mb1 :=
      fun h => h1 ((E.congrOfK_mem1 e Mbar' hM k).1 h)
    by_cases h2 : k ∈ E.Mb2
    · have h2' := (E.congrOfK_mem2 e Mbar' hM k).2 h2
      have e1 : amalgamMap (E.congrOf e Mbar' hM).b1 (E.congrOf e Mbar' hM).b2
          (E.congrOfK e Mbar' hM k) = (E.congrOf e Mbar' hM).b2 ⟨_, h2'⟩ := by
        unfold amalgamMap
        simp [h1', h2']
      have e2 : amalgamMap E.b1 E.b2 k = E.b2 ⟨k, h2⟩ := by
        unfold amalgamMap
        simp [h1, h2]
      rw [e1, e2, E.congrOfK_b2 e Mbar' hM k h2 h2']
    · have h2' : E.congrOfK e Mbar' hM k ∉ (E.congrOf e Mbar' hM).Mb2 :=
        fun h => h2 ((E.congrOfK_mem2 e Mbar' hM k).1 h)
      unfold amalgamMap
      simp [h1, h2, h1', h2']

@[expose] noncomputable def congrOfLocIso : LocIso E (E.congrOf e Mbar' hM) where
  ψ := E.congrOfK e Mbar' hM
  mem1 := E.congrOfK_mem1 e Mbar' hM
  mem2 := E.congrOfK_mem2 e Mbar' hM
  amalg := E.amalgamMap_congrOfK e Mbar' hM

end CFSG.Quasithin.H13.F431.LieExt

namespace CFSG.Quasithin.H13.F431.LieAmalgamExt

variable {D : Type} [Group D] (A : LieAmalgamExt D)

theorem K_le_Mbar : A.K ≤ A.Mbar := sup_le inf_le_left inf_le_left

theorem N1_eq : A.N1 = A.K ⊓ autStab A.P1 :=
  le_antisymm (le_inf A.N1_le_K inf_le_right)
    (inf_le_inf_right _ A.K_le_Mbar)

theorem N2_eq : A.N2 = A.K ⊓ autStab A.P2 :=
  le_antisymm (le_inf A.N2_le_K inf_le_right)
    (inf_le_inf_right _ A.K_le_Mbar)

theorem Mb1_eq_std : A.Mb1 = (A.K ⊓ autStab A.P1).subgroupOf A.K := by
  rw [← A.N1_eq]

theorem Mb2_eq_std : A.Mb2 = (A.K ⊓ autStab A.P2).subgroupOf A.K := by
  rw [← A.N2_eq]

theorem range_conj_le_K (hsup : A.P1 ⊔ A.P2 = ⊤) :
    (MulAut.conj : D →* MulAut D).range ≤ A.K := by
  have hc : ∀ {P : Subgroup D} {p : D}, p ∈ P → (MulAut.conj p : MulAut D) ∈ autStab P :=
    fun {P p} hp x => by
      rw [MulAut.conj_apply]
      constructor
      · intro hx
        exact P.mul_mem (P.mul_mem hp hx) (P.inv_mem hp)
      · intro hx
        have := P.mul_mem (P.mul_mem (P.inv_mem hp) hx) hp
        simpa [mul_assoc] using this
  have h1 : A.P1.map (MulAut.conj : D →* MulAut D) ≤ A.N1 := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨A.inn_le ⟨p, rfl⟩, hc hp⟩
  have h2 : A.P2.map (MulAut.conj : D →* MulAut D) ≤ A.N2 := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨A.inn_le ⟨p, rfl⟩, hc hp⟩
  have h : (⊤ : Subgroup D).map (MulAut.conj : D →* MulAut D) ≤ A.K := by
    rw [← hsup, Subgroup.map_sup]
    exact sup_le (h1.trans A.N1_le_K) (h2.trans A.N2_le_K)
  rintro _ ⟨d, rfl⟩
  exact h ⟨d, Subgroup.mem_top d, rfl⟩

@[expose] def toLieExt : LieExt D A.N1 A.N2 :=
  { A with iso := CFSG.Quasithin.H13.F431.U42.Am.ofSubgroupsCongr rfl rfl }

end CFSG.Quasithin.H13.F431.LieAmalgamExt
