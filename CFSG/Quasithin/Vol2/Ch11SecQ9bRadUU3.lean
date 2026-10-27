module

public import CFSG.Quasithin.Vol2.Ch11SecQ9bRadUU2
public import CFSG.Quasithin.Vol2.Ch11SecA12Cart
public import CFSG.Quasithin.Vol2.Ch11SecAVi2
public import CFSG.Quasithin.Vol2.Ch1Sec3Basic
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin SecS

variable {G : Type} [Group G] [Finite G] {T L I V₁ V₂ X U K : Subgroup G} {n : ℕ}

namespace C11P9B

theorem comm_of_mem_fsuV (h : Hyp11 G T L I n) {a b : G} (ha : a ∈ fsuV T I)
    (hb : b ∈ fsuV T I) : a * b = b * a := by
  obtain ⟨hc, -⟩ := isElemAbelian_fsuV h
  have h2 := hc.is_comm.comm (⟨a, ha⟩ : ↥(fsuV T I)) ⟨b, hb⟩
  exact congrArg Subtype.val h2

theorem mem_normalizer_sup' {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  refine mem_normalizer_of_map_le (N := A ⊔ B) ?_
  rw [Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hA a).mp ha)
  · rintro _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hB b).mp hb)

theorem L_le_normalizer_cV (h : Hyp11 G T L I n) :
    L ≤ Subgroup.normalizer
      ((fsuV T I ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := fun _ hl =>
  Subgroup.inf_normalizer_le_normalizer_inf
    ⟨L_le_normalizer_fsuV h hl, mem_normalizer_centralizer (Subgroup.le_normalizer hl)⟩

theorem le_inf_sup_of_sup_eq (hN : NatFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hV₁ : IsVi T L I n 1 V₁) (hV₂ : IsVi T L I n 2 V₂)
    (hUV : U ⊔ (fsuV T I ⊓ Subgroup.centralizer (L : Set G)) = V₂) :
    V₁ ≤ (V₁ ⊓ U) ⊔ (fsuV T I ⊓ Subgroup.centralizer (L : Set G)) := by
  have hUV' : U ≤ fsuV T I := (le_V2_of_sup_eq hUV).trans (IsVi.le_fsuV hV₂)
  have hZU : fsuV T I ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.normalizer (U : Set G) :=
    fun z hz => Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr
      fun u hu => comm_of_mem_fsuV h (hUV' hu) hz.1)
  intro v hv
  have hv2 : v ∈ U ⊔ (fsuV T I ⊓ Subgroup.centralizer (L : Set G)) := by
    rw [hUV]
    exact IsVi.mono₁₂ hN h1102 h hV₁ hV₂ hv
  obtain ⟨u, hu, z, hz, rfl⟩ := (Ch1Sec3.mem_sup_iff_of_le_normalizer hZU).1 hv2
  have huV₁ : u ∈ V₁ := by
    have := V₁.mul_mem hv (V₁.inv_mem (IsVi.cV_le hV₁ hz))
    simpa using this
  exact Subgroup.mul_mem_sup ⟨huV₁, hu⟩ hz

theorem inf_sup_eq_of_sup_eq (hN : NatFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hV₁ : IsVi T L I n 1 V₁) (hV₂ : IsVi T L I n 2 V₂)
    (hUV : U ⊔ (fsuV T I ⊓ Subgroup.centralizer (L : Set G)) = V₂) :
    (V₁ ⊓ U) ⊔ (fsuV T I ⊓ Subgroup.centralizer (L : Set G)) = V₁ :=
  le_antisymm (sup_le inf_le_left (IsVi.cV_le hV₁)) (le_inf_sup_of_sup_eq hN h1102 h hV₁ hV₂ hUV)

theorem point_ne_bot (hN : NatFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hV₁ : IsVi T L I n 1 V₁) (hV₂ : IsVi T L I n 2 V₂)
    (hUV : U ⊔ (fsuV T I ⊓ Subgroup.centralizer (L : Set G)) = V₂) : V₁ ⊓ U ≠ ⊥ := by
  intro h0
  have h1 := inf_sup_eq_of_sup_eq hN h1102 h hV₁ hV₂ hUV
  rw [h0, bot_sup_eq] at h1
  have h2 := IsVi.relIndex_eq hV₁
  rw [h1, Subgroup.relIndex_self] at h2
  have h3 : 1 < 2 ^ (n * 1) := Nat.one_lt_two_pow (by have := h.one_lt; omega)
  omega

omit [Finite G] in
theorem T_le_normalizer_point (hV₁ : IsVi T L I n 1 V₁)
    (hTU : T ≤ Subgroup.normalizer (U : Set G)) :
    T ≤ Subgroup.normalizer ((V₁ ⊓ U : Subgroup G) : Set G) := fun _ ht =>
  Subgroup.inf_normalizer_le_normalizer_inf ⟨IsVi.le_normalizer hV₁ ht, hTU ht⟩

theorem xOne_le_normalizer_point (hN : NatFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hV₁ : IsVi T L I n 1 V₁) (hV₂ : IsVi T L I n 2 V₂) (hX : IsCartanX T L X)
    (hLU : L ⊓ Subgroup.normalizer (V₂ : Set G) ≤ Subgroup.normalizer (U : Set G)) :
    xOne X (LOf L V₁) ≤ Subgroup.normalizer ((V₁ ⊓ U : Subgroup G) : Set G) := fun _ hx =>
  Subgroup.inf_normalizer_le_normalizer_inf ⟨xOne_le_normalizer_V1 hN h1102 h hV₁ hX hx,
    hLU ⟨(hX.1 hx.1).1, cartan_le_normalizer_Vi hN h1102 h (Or.inr rfl) hV₂ hX hx.1⟩⟩

theorem xOne_inf_centralizer_point (hC : CartanFacts) (hF : Facts12) (hN : NatFacts)
    (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁)
    (hV₂ : IsVi T L I n 2 V₂) (hX : IsCartanX T L X)
    (hUV : U ⊔ (fsuV T I ⊓ Subgroup.centralizer (L : Set G)) = V₂) :
    xOne X (LOf L V₁) ⊓ Subgroup.centralizer ((V₁ ⊓ U : Subgroup G) : Set G) = ⊥ := by
  rw [eq_bot_iff, ← xOne_inf_centralizer hC hF hN h1102 h hV₁ hV₂ hX]
  rintro x ⟨hx, hxC⟩
  refine ⟨hx, ?_⟩
  rw [← inf_sup_eq_of_sup_eq hN h1102 h hV₁ hV₂ hUV]
  exact mem_centralizer_sup hxC (Subgroup.mem_centralizer_iff.mpr fun z hz =>
    (Subgroup.mem_centralizer_iff.mp hz.2 x (hX.1 hx.1).1).symm)

theorem inf_normalizer_point_le (hN : NatFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hV₁ : IsVi T L I n 1 V₁) (hV₂ : IsVi T L I n 2 V₂)
    (hUV : U ⊔ (fsuV T I ⊓ Subgroup.centralizer (L : Set G)) = V₂) :
    L ⊓ Subgroup.normalizer ((V₁ ⊓ U : Subgroup G) : Set G) ≤
      Subgroup.normalizer (V₁ : Set G) := by
  rintro l ⟨hl, hl₀⟩
  have := mem_normalizer_sup' hl₀ (L_le_normalizer_cV h hl)
  rwa [inf_sup_eq_of_sup_eq hN h1102 h hV₁ hV₂ hUV] at this

theorem inf_normalizer_U_le (h : Hyp11 G T L I n)
    (hUV : U ⊔ (fsuV T I ⊓ Subgroup.centralizer (L : Set G)) = V₂) :
    L ⊓ Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (V₂ : Set G) := by
  rintro l ⟨hl, hlU⟩
  have := mem_normalizer_sup' hlU (L_le_normalizer_cV h hl)
  rwa [hUV] at this

theorem not_le_normalizer_U (hN : NatFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hV₂ : IsVi T L I n 2 V₂)
    (hUV : U ⊔ (fsuV T I ⊓ Subgroup.centralizer (L : Set G)) = V₂)
    (hLU : L ⊓ Subgroup.normalizer (V₂ : Set G) ≤ Subgroup.normalizer (U : Set G))
    (hK : K ∈ cComp (Subgroup.normalizer (U : Set G))) (hlt : LOf L V₂ < K) :
    ¬ K ≤ Subgroup.normalizer (L : Set G) := by
  intro hKM
  have hKN := le_of_mem_cComp hK
  have hL₂ : LOf L V₂ ≤ L ⊓ Subgroup.normalizer (U : Set G) :=
    le_inf ((perfectCore_le _).trans inf_le_left) ((perfectCore_le _).trans hLU)
  have hKX : K ≤ L ⊓ Subgroup.normalizer (U : Set G) := by
    refine le_of_cComp_of_perfect hK inf_le_right ?_ (lOf_ne_bot hN h1102 h hV₂ (Or.inr rfl))
      (perfectCore_perfect _) hlt.le hL₂
    exact (le_inf hKM (hKN.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hKL : K ≤ LOf L V₂ := by
    rw [← perfectCore_eq_self_of_perfect (perfect_of_mem_cComp hK)]
    exact perfectCore_mono (hKX.trans (le_inf inf_le_left (inf_normalizer_U_le h hUV)))
  exact hlt.not_ge hKL

theorem charTwo_normalizer_W (h : Hyp11 G T L I n) {W : Subgroup G} (hWV : W ≤ fsuV T I)
    (hW : W ≠ ⊥) (hTW : T ≤ Subgroup.normalizer (W : Set G)) :
    QuasithinUnique.CharTwo (Subgroup.normalizer (W : Set G)) :=
  charTwo_of_inH h.fsu.qtke.2.1 (h.fsu.sylow.1.toSylow h.fsu.sylow.2)
    ⟨hTW, pCoreOf_normalizer_ne_bot_of_le h hWV hW⟩

theorem charTwo_of_cComp_W (h : Hyp11 G T L I n) {W : Subgroup G} (hWV : W ≤ fsuV T I)
    (hW : W ≠ ⊥) (hTW : T ≤ Subgroup.normalizer (W : Set G))
    (hK : K ∈ cComp (Subgroup.normalizer (W : Set G)))
    (hNK : Subgroup.normalizer (W : Set G) ≤ Subgroup.normalizer (K : Set G)) :
    QuasithinUnique.CharTwo K := by
  have hle := le_of_mem_cComp hK
  have hn : (K.subgroupOf (Subgroup.normalizer (W : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr hNK
  exact QuasithinUnique.CharTwo.of_isSubnormal (charTwo_normalizer_W h hWV hW hTW) hle
    hn.isSubnormal

end C11P9B

end CFSG.Quasithin.Vol2.Ch11.SecA
