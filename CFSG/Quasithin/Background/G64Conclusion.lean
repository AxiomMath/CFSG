module

public import CFSG.Quasithin.Background.G64ProofBasic
public import CFSG.Quasithin.Background.G64NatTop

public section

namespace CFSG.Quasithin.G64

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
  CFSG.Assembly.LowTwoRank

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {a : MulAut V}

theorem map_conj_classK {g : MulAut V} (hg : g ∈ G) :
    (conjClosure (Subgroup.zpowers a) G).map (MulAut.conj g).toMonoidHom =
      conjClosure (Subgroup.zpowers a) G :=
  Subgroup.mem_normalizer_iff_map_conj_eq.1 (le_normalizer_conjClosure _ G hg)

theorem mem_classK : a ∈ conjClosure (Subgroup.zpowers a) G :=
  le_conjClosure _ _ (Subgroup.mem_zpowers a)

theorem conclusion_of_single (h : Hyp61 G a) (hGK : G = conjClosure (Subgroup.zpowers a) G)
    (hmod : ModuleType (conjClosure (Subgroup.zpowers a) G) ⊤)
    (h4 : (∃ T, IsSylowTwoOf T G ∧ a ∈ T ∧ ∀ x ∈ T, x * a = a * x) → CentralType ↥G) :
    Conclusion G a := by
  set K := conjClosure (Subgroup.zpowers a) G with hK
  have hKV : commV K = ⊤ := commV_classK h
  refine ⟨1, fun _ => K, by norm_num, iSup_const, iSupIndep_subsingleton _,
    fun i j hij => absurd (Subsingleton.elim i j) hij, by rw [iSup_const, hKV],
    fun i j hij => absurd (Subsingleton.elim i j) hij, ⟨one_pos, mem_classK⟩,
    fun g hg _ => ⟨0, map_conj_classK hg⟩, fun _ _ => ⟨1, G.one_mem, map_conj_classK G.one_mem⟩,
    fun _ => by rw [hKV]; exact hmod, Or.inl ⟨rfl, hGK⟩, fun hT => ⟨rfl, hGK, h4 hT⟩⟩

theorem map_conj_inv_of_map_conj {M : Type*} [Group M] {A B : Subgroup M} {g : M}
    (h : A.map (MulAut.conj g).toMonoidHom = B) : B.map (MulAut.conj g⁻¹).toMonoidHom = A := by
  rw [← h, Subgroup.map_map]
  convert Subgroup.map_id A using 2
  ext x
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulAut.conj_apply, MonoidHom.id_apply]
  group

theorem conclusion_of_pair {K₀ K₁ : Subgroup (MulAut V)}
    (hK : K₀ ⊔ K₁ = conjClosure (Subgroup.zpowers a) G) (hdis : K₀ ⊓ K₁ = ⊥)
    (hcomm : ∀ x ∈ K₀, ∀ y ∈ K₁, x * y = y * x) (hV : commV K₀ ⊔ commV K₁ = ⊤)
    (hfix₀ : commV K₁ ≤ fixV K₀) (hfix₁ : commV K₀ ≤ fixV K₁) (ha : a ∈ K₀)
    (hperm : ∀ g ∈ G, (K₀.map (MulAut.conj g).toMonoidHom = K₀ ∧
        K₁.map (MulAut.conj g).toMonoidHom = K₁) ∨
      (K₀.map (MulAut.conj g).toMonoidHom = K₁ ∧ K₁.map (MulAut.conj g).toMonoidHom = K₀))
    (hmod₀ : ModuleType K₀ (commV K₀)) (hmod₁ : ModuleType K₁ (commV K₁))
    (hfac₀ : FactorType K₀) (hfac₁ : FactorType K₁) {t : MulAut V} (htG : t ∈ G) (ht1 : t ≠ 1)
    (ht2 : t ^ 2 = 1) (hGt : G = conjClosure (Subgroup.zpowers a) G ⊔ Subgroup.zpowers t)
    (ht₀ : K₀.map (MulAut.conj t).toMonoidHom = K₁)
    (h4 : ¬ ∃ T, IsSylowTwoOf T G ∧ a ∈ T ∧ ∀ x ∈ T, x * a = a * x) :
    Conclusion G a := by
  set Ks : Fin 2 → Subgroup (MulAut V) := ![K₀, K₁] with hKs
  have hfin : ∀ i : Fin 2, i = 0 ∨ i = 1 := fun i => by fin_cases i <;> simp
  have ht₁ : K₁.map (MulAut.conj t).toMonoidHom = K₀ := by
    have h1 := map_conj_inv_of_map_conj ht₀
    have ht' : t⁻¹ = t := by rw [inv_eq_iff_mul_eq_one, ← sq, ht2]
    rwa [ht'] at h1
  refine ⟨2, Ks, le_rfl, ?_, ?_, fun i j hij => ?_, ?_, fun i j hij => ?_,
    ⟨two_pos, show a ∈ K₀ from ha⟩,
    fun g hg i => ?_, fun i j => ?_, fun i => ?_, Or.inr ⟨rfl, fun i => ?_, t, htG, ht1, ht2, hGt,
      fun i j hij => ?_⟩, fun hT => absurd hT h4⟩
  · rw [G6.iSup_fin_two]
    exact hK
  · rw [iSupIndep_pair (by decide : (0 : Fin 2) ≠ 1) hfin]
    exact disjoint_iff.2 hdis
  · rcases hfin i with rfl | rfl <;> rcases hfin j with rfl | rfl
    · exact absurd rfl hij
    · exact hcomm
    · exact fun x hx y hy => (hcomm y hy x hx).symm
    · exact absurd rfl hij
  · rw [G6.iSup_fin_two]
    exact hV
  · rcases hfin i with rfl | rfl <;> rcases hfin j with rfl | rfl
    · exact absurd rfl hij
    · exact hfix₀
    · exact hfix₁
    · exact absurd rfl hij
  · rcases hperm g hg with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rcases hfin i with rfl | rfl
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
    · exact ⟨1, h0⟩
    · exact ⟨0, h1⟩
  · have hid : ∀ A : Subgroup (MulAut V), A.map (MulAut.conj (1 : MulAut V)).toMonoidHom = A :=
      fun A => by
        convert Subgroup.map_id A using 2
        ext x
        simp
    rcases hfin i with rfl | rfl <;> rcases hfin j with rfl | rfl
    · exact ⟨1, G.one_mem, hid K₀⟩
    · exact ⟨t, htG, ht₀⟩
    · exact ⟨t, htG, ht₁⟩
    · exact ⟨1, G.one_mem, hid K₁⟩
  · rcases hfin i with rfl | rfl
    · exact hmod₀
    · exact hmod₁
  · rcases hfin i with rfl | rfl
    · exact hfac₀
    · exact hfac₁
  · rcases hfin i with rfl | rfl <;> rcases hfin j with rfl | rfl
    · exact absurd rfl hij
    · exact ht₀
    · exact ht₁
    · exact absurd rfl hij

theorem conclusion_of_case2 [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) (h : Hyp61 G a)
    (hC : B56Case2 (conjClosure (Subgroup.zpowers a) G)) : Conclusion G a := by
  set K := conjClosure (Subgroup.zpowers a) G with hK
  obtain ⟨⟨e⟩, -, hcard⟩ := hC
  have hKV : commV K = ⊤ := commV_classK h
  rw [hKV, Subgroup.card_top] at hcard
  obtain ⟨π, hπ⟩ := realizesVia_top_of_card hV2 hcard
  have hinj := natSL_injective hπ
  let θ : ↥(StatedSL 2 (ZMod 2)) ≃* ↥(⊤ : Subgroup (MulAut V)) :=
    MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
  have htop6 : Nat.card ↥(⊤ : Subgroup (MulAut V)) = 6 := by
    rw [← Nat.card_congr θ.toEquiv]
    exact card_statedSL_two (by simp)
  have hK6 : Nat.card K = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hKtop : K = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hK6, ← htop6, Subgroup.card_top]
  have hGK : G = K := le_antisymm (by rw [hKtop]; exact le_top) (classK_le h)
  refine conclusion_of_single h hGK ?_ fun _ => ?_
  · left
    refine ⟨2, le_rfl, by norm_num, ZMod 2, inferInstance, inferInstance, by simp, ?_⟩
    rw [← hK, hKtop]
    exact ⟨π, hπ⟩
  · left
    refine ⟨2, le_rfl, by norm_num, ⟨?_⟩⟩
    rw [hGK, hKtop]
    exact θ.symm

end CFSG.Quasithin.G64
