module

public import CFSG.RankThree.PartTwo.Sec19.Item1923Defs

public section

namespace CFSG.RankThree.PartTwo.Late.KFParSp6

open CFSG

theorem oTwoP_map_mulEquiv (p : ℕ) {A B : Type} [Group A] [Group B] (f : A ≃* B) :
    (Sec4.oTwoP p A).map f.toMonoidHom = Sec4.oTwoP p B := by
  obtain ⟨N, hN⟩ : ∃ N : Subgroup A, N = CFSG.pCore 2 A := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : Subgroup B, M = CFSG.pCore 2 B := ⟨_, rfl⟩
  haveI hNn : N.Normal := by rw [hN]; infer_instance
  haveI hMn : M.Normal := by rw [hM]; infer_instance
  have h2 : N.map f.toMonoidHom = M := by
    rw [hN, hM]
    exact CFSG.pCore_map_iso 2 f
  let q := QuotientGroup.congr N M f h2
  have hq : (CFSG.pCore p (A ⧸ N)).map q.toMonoidHom = CFSG.pCore p (B ⧸ M) :=
    CFSG.pCore_map_iso p q
  have hOA : Sec4.oTwoP p A = (CFSG.pCore p (A ⧸ N)).comap (QuotientGroup.mk' N) := by
    subst hN
    rfl
  have hOB : Sec4.oTwoP p B = (CFSG.pCore p (B ⧸ M)).comap (QuotientGroup.mk' M) := by
    subst hM
    rfl
  have hqmk : ∀ x : A, q.toMonoidHom (QuotientGroup.mk' N x) = QuotientGroup.mk' M (f x) :=
    fun x => rfl
  rw [hOA, hOB]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [SetLike.mem_coe, Subgroup.mem_comap] at hx ⊢
    have hm : q.toMonoidHom (QuotientGroup.mk' N x) ∈ CFSG.pCore p (B ⧸ M) := by
      rw [← hq]
      exact Subgroup.mem_map_of_mem _ hx
    rw [hqmk] at hm
    exact hm
  · intro hy
    simp only [SetLike.mem_coe, Subgroup.mem_comap] at hy
    have hyy : q.toMonoidHom (QuotientGroup.mk' N (f.symm y)) ∈ CFSG.pCore p (B ⧸ M) := by
      rw [hqmk, MulEquiv.apply_symm_apply]
      exact hy
    rw [← hq] at hyy
    obtain ⟨z, hz, hzeq⟩ := Subgroup.mem_map.mp hyy
    have hzA : z = QuotientGroup.mk' N (f.symm y) := q.injective hzeq
    refine ⟨f.symm y, ?_, by simp⟩
    simp only [SetLike.mem_coe, Subgroup.mem_comap]
    rw [← hzA]
    exact hz

theorem congr_conj_eq {X Y : Type} [Group X] [Group Y] (ϕ : X ≃* Y) (x : X) :
    MulAut.congr ϕ (MulAut.conj x) = MulAut.conj (ϕ x) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem isProperParabolic_map {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (ϕ : X ≃* Y) {P : Subgroup X} (hP : Sec19.IsProperParabolic P) :
    Sec19.IsProperParabolic (P.map ϕ.toMonoidHom) := by
  obtain ⟨hne, T, hT⟩ := hP
  refine ⟨?_, ?_⟩
  · intro htop
    apply hne
    ext x
    refine ⟨fun _ => Subgroup.mem_top _, fun _ => ?_⟩
    have hx : ϕ x ∈ P.map ϕ.toMonoidHom := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hyx' : y = x := ϕ.injective hyx
    rw [← hyx']
    exact hy
  · have hTp : IsPGroup 2 ((T : Subgroup X).map ϕ.toMonoidHom) :=
      T.isPGroup'.map ϕ.toMonoidHom
    have hidx : ¬ 2 ∣ ((T : Subgroup X).map ϕ.toMonoidHom).index := by
      have h : ((T : Subgroup X).map ϕ.toMonoidHom).index = (T : Subgroup X).index :=
        Subgroup.index_map_equiv (H := (T : Subgroup X)) ϕ
      rw [h]
      exact Sylow.not_dvd_index T
    refine ⟨hTp.toSylow hidx, ?_⟩
    rw [IsPGroup.toSylow_coe]
    intro y hy
    obtain ⟨x, rfl⟩ := ϕ.surjective y
    have hxN : x ∈ Subgroup.normalizer ((T : Subgroup X) : Set X) := by
      rw [Subgroup.mem_normalizer_iff] at hy ⊢
      intro h
      have key := hy (ϕ h)
      have e1 : ϕ x * ϕ h * (ϕ x)⁻¹ = ϕ (x * h * x⁻¹) := by
        simp [map_mul, map_inv]
      rw [e1, Subgroup.mem_map_equiv, Subgroup.mem_map_equiv] at key
      simp only [MulEquiv.symm_apply_apply] at key
      exact key
    exact Subgroup.mem_map_of_mem _ (hT hxN)

@[expose] def NSPremises (X : Type) [Group X] (P : Subgroup X) (D : Subgroup (MulAut X))
    (t : MulAut X) : Prop :=
  ParabolicShape X P ∧ D ≤ P.map (MulAut.conj : X →* MulAut X) ∧
    CFSG.Assembly.IsElemAbelian 3 D ∧ Nat.card D = 9 ∧
    D ≤ (Sec4.oTwoP 3 ↥(P.map (MulAut.conj : X →* MulAut X))).map
      (P.map (MulAut.conj : X →* MulAut X)).subtype ∧
    t ∈ P.map (MulAut.conj : X →* MulAut X) ∧
    t ∈ Subgroup.normalizer (D : Set (MulAut X))

theorem isElemAbelian_map_injective {G H : Type} [Group G] [Group H] (p : ℕ) {E : Subgroup G}
    (hE : CFSG.Assembly.IsElemAbelian p E) (f : G →* H) (hf : Function.Injective f) :
    CFSG.Assembly.IsElemAbelian p (E.map f) := by
  obtain ⟨hcomm, hexp⟩ := hE
  refine ⟨?_, ?_⟩
  · refine ⟨⟨fun x y => ?_⟩⟩
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.mp y.2
    have hab : a * b = b * a := by
      have := hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
      exact congrArg Subtype.val this
    apply Subtype.ext
    show (x : H) * (y : H) = (y : H) * (x : H)
    rw [← hax, ← hby, ← map_mul, ← map_mul, hab]
  · intro x hx
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hx
    rw [← hax, ← map_pow, hexp a ha, map_one]

theorem nsPremises_map {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y] (e : X ≃* Y)
    (hY : ¬ Nonempty (Y ≃* alternatingGroup (Fin 10)))
    {P : Subgroup X} {D : Subgroup (MulAut X)} {t : MulAut X} (h : NSPremises X P D t) :
    NSPremises Y (P.map e.toMonoidHom) (D.map (MulAut.congr e).toMonoidHom)
      (MulAut.congr e t) := by
  obtain ⟨hsh, hDP, hD, hD9, hDO, htP, htN⟩ := h
  have hQ : (P.map (MulAut.conj : X →* MulAut X)).map (MulAut.congr e).toMonoidHom =
      (P.map e.toMonoidHom).map (MulAut.conj : Y →* MulAut Y) := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun x => ?_
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
    exact congr_conj_eq e x
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hsh with ⟨_, hP⟩ | ⟨⟨e10⟩, _⟩
    · exact Or.inl ⟨not_nonempty_iff.mp hY, isProperParabolic_map e hP⟩
    · exact absurd ⟨e.symm.trans e10⟩ hY
  · intro d' hd'
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hd'
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp (hDP hd)
    show (MulAut.congr e) (MulAut.conj x) ∈ _
    rw [congr_conj_eq]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hx)
  · exact isElemAbelian_map_injective 3 hD _ (MulAut.congr e).injective
  · rw [Subgroup.card_map_of_injective (MulAut.congr e).injective, hD9]
  · intro d' hd'
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hd'
    obtain ⟨x, hx, hxd⟩ := Subgroup.mem_map.mp (hDO hd)
    let ψ : (P.map (MulAut.conj : X →* MulAut X)) ≃*
        ((P.map e.toMonoidHom).map (MulAut.conj : Y →* MulAut Y)) :=
      (MulEquiv.subgroupMap (MulAut.congr e) _).trans (MulEquiv.subgroupCongr hQ)
    have hψ := oTwoP_map_mulEquiv 3 ψ
    refine Subgroup.mem_map.mpr ⟨ψ x, ?_, ?_⟩
    · rw [← hψ]
      exact Subgroup.mem_map_of_mem _ hx
    · rw [← hxd]
      rfl
  · rw [← hQ]
    exact Subgroup.mem_map_of_mem _ htP
  · rw [Subgroup.mem_normalizer_iff]
    intro h'
    constructor
    · intro hh
      obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hh
      have h1 : t * d * t⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp htN d).mp hd
      have e1 : (MulAut.congr e) t * (MulAut.congr e).toMonoidHom d * ((MulAut.congr e) t)⁻¹ =
          (MulAut.congr e).toMonoidHom (t * d * t⁻¹) := by
        rw [map_mul, map_mul, map_inv]
        rfl
      rw [e1]
      exact Subgroup.mem_map_of_mem _ h1
    · intro hh
      obtain ⟨d, hd, hdeq⟩ := Subgroup.mem_map.mp hh
      have hz : t⁻¹ * d * t⁻¹⁻¹ ∈ D :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htN) d).mp hd
      refine Subgroup.mem_map.mpr ⟨t⁻¹ * d * t⁻¹⁻¹, hz, ?_⟩
      have hh' : h' =
          ((MulAut.congr e) t)⁻¹ * (MulAut.congr e).toMonoidHom d * (MulAut.congr e) t := by
        rw [hdeq]
        group
      rw [hh']
      simp only [map_mul, map_inv, inv_inv, MulEquiv.coe_toMonoidHom]

end CFSG.RankThree.PartTwo.Late.KFParSp6

end
