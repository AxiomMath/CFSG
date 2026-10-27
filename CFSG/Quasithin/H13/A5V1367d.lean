module

public import CFSG.Quasithin.H13.A5V1367c

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative

theorem pact_W4_of_fix_E12 : ∀ σ : Equiv.Perm (Fin 5), pact σ E12 = E12 →
    pact σ W4 = W4 ∨ pact σ W4 = Multiplicative.ofAdd (wA 2) ∨
      pact σ W4 = Multiplicative.ofAdd (wA 3) := by
  decide +kernel

theorem exists_mul_normalizer_of_sylow {Γ : Type} [Group Γ] [Finite Γ] {H N S : Subgroup Γ}
    (hNH : N ≤ H) (hHN : H ≤ Subgroup.normalizer (N : Set Γ)) (hS : IsSylowTwoOf S N)
    {h : Γ} (hh : h ∈ H) : ∃ n ∈ N, ∃ k ∈ H ⊓ Subgroup.normalizer (S : Set Γ), h = n * k := by
  have hx := B6.frattini_two hNH hHN hS hh
  have hle : H ⊓ Subgroup.normalizer (S : Set Γ) ≤ Subgroup.normalizer (N : Set Γ) :=
    inf_le_left.trans hHN
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left N _ hle] at hx
  obtain ⟨n, hn, k, hk, rfl⟩ := Set.mem_mul.mp hx
  exact ⟨n, hn, k, hk, rfl⟩

section Triv

variable {U : Type*} [CommGroup U]

theorem mul_self_eq_one_of_triv (hU : ∀ u : U, u * u = 1) {J : Subgroup (MulAut U)}
    (h : ∀ j ∈ J, ∀ u : U, j u * u⁻¹ ∈ fixV J) {j : MulAut U} (hj : j ∈ J) : j * j = 1 := by
  ext u
  rw [MulAut.mul_apply, MulAut.one_apply]
  have hc := h j hj u
  have hju : j u = (j u * u⁻¹) * u := by rw [inv_mul_cancel_right]
  calc j (j u) = j ((j u * u⁻¹) * u) := by rw [← hju]
    _ = j (j u * u⁻¹) * j u := map_mul _ _ _
    _ = (j u * u⁻¹) * j u := by rw [(mem_fixV.mp hc) j hj]
    _ = (j u * u⁻¹) * ((j u * u⁻¹) * u) := by rw [← hju]
    _ = ((j u * u⁻¹) * (j u * u⁻¹)) * u := by rw [← mul_assoc]
    _ = u := by rw [hU, one_mul]

theorem triv_of_mem_W2 {J G₁ G₂ : Subgroup (MulAut U)} {W₁ W₂ : Subgroup U}
    (hsup : G₁ ⊔ G₂ = J) (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) (hW₁ : commV G₁ ≤ W₁)
    (hinv₂ : ∀ g ∈ J, ∀ w ∈ W₂, g w ∈ W₂) (hinf : W₁ ⊓ W₂ = fixV J) {t : MulAut U}
    (htJ : ∀ j ∈ J, t⁻¹ * j * t ∈ J) (htG : ∀ g ∈ G₂, t⁻¹ * g * t ∈ G₁) {u : U}
    (htu : t u = u) (hu : u ∈ W₂) : ∀ j ∈ J, j u * u⁻¹ ∈ fixV J := by
  have hG₁J : G₁ ≤ J := hsup ▸ le_sup_left
  have htC : ∀ c ∈ fixV J, t c ∈ fixV J := by
    intro c hc' j hj
    have h1 := (mem_fixV.mp hc') _ (htJ j hj)
    calc j (t c) = t ((t⁻¹ * j * t) c) := by
          rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
      _ = t c := by rw [h1]
  have hG₁ : ∀ g ∈ G₁, g u * u⁻¹ ∈ fixV J := by
    intro g hg
    rw [← hinf]
    exact ⟨hW₁ (Subgroup.subset_closure ⟨g, hg, u, rfl⟩),
      W₂.mul_mem (hinv₂ g (hG₁J hg) u hu) (W₂.inv_mem hu)⟩
  have hG₂ : ∀ g ∈ G₂, g u * u⁻¹ ∈ fixV J := by
    intro g hg
    have h1 := htC _ (hG₁ _ (htG g hg))
    have e : t ((t⁻¹ * g * t) u * u⁻¹) = g u * u⁻¹ := by
      rw [map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply, htu, MulAut.apply_inv_self]
    rw [← e]
    exact h1
  intro j hj
  obtain ⟨a, ha, b, hb, rfl⟩ := S153L.comp_exists_mul hc (hsup ▸ hj)
  have hb' := hG₂ b hb
  have ha' := hG₁ a ha
  have e : (a * b) u * u⁻¹ = a (b u * u⁻¹) * (a u * u⁻¹) := by
    rw [MulAut.mul_apply]
    rw [show b u = (b u * u⁻¹) * u by rw [inv_mul_cancel_right]]
    rw [map_mul, inv_mul_cancel_right, map_mul]
    group
  rw [e, (mem_fixV.mp hb') a (hG₁J ha)]
  exact (fixV J).mul_mem hb' ha'

end Triv

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem false_of_four_conj {a : Fin 4 → G} (haN : ∀ i, a i ∈ Subgroup.normalizer (V : Set G))
    (hav : ∀ i, a i ∈ Subgroup.centralizer ({S.v12} : Set G))
    (h : ∀ i j : Fin 4, i ≠ j → a i * S.z * (a i)⁻¹ ≠ a j * S.z * (a j)⁻¹) : False := by
  classical
  have hmem : ∀ i, a i * S.z * (a i)⁻¹ ∈ V := fun i =>
    (Subgroup.mem_normalizer_iff.mp (haN i) S.z).mp S.z_mem_V
  let f : Fin 4 → W5 := fun i => S.frame.ψ ⟨a i * S.z * (a i)⁻¹, hmem i⟩
  have hf : ∀ i ∈ (Finset.univ : Finset (Fin 4)),
      f i ∈ ({W4, Multiplicative.ofAdd (wA 2), Multiplicative.ofAdd (wA 3)} : Finset W5) := by
    intro i _
    have hconj : a i * S.v12 * (a i)⁻¹ = S.v12 := by
      have := Subgroup.mem_centralizer_iff.mp (hav i) S.v12 (Set.mem_singleton _)
      rw [← this, mul_inv_cancel_right]
    have hfix : pact (S.frame.ρ ⟨a i, haN i⟩) E12 = E12 := by
      have h0 := (S.conj_eq_iff ⟨a i, haN i⟩ ⟨S.v12, S.v12_mem_V⟩).mp hconj
      rwa [S.psi_v12] at h0
    have hψ : f i = pact (S.frame.ρ ⟨a i, haN i⟩) W4 := by
      have := S.psi_conj ⟨a i, haN i⟩ ⟨S.z, S.z_mem_V⟩
      rw [S.psi_z] at this
      exact this
    rcases pact_W4_of_fix_E12 _ hfix with h1 | h1 | h1 <;> simp [hψ, h1]
  obtain ⟨i, -, j, -, hij, hfij⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (by rw [Finset.card_univ, Fintype.card_fin]; exact Finset.card_le_three.trans_lt (by norm_num))
    hf
  exact h i j hij (congrArg Subtype.val (S.frame.ψ.injective hfij))

@[expose] noncomputable def preGv (Q : Subgroup (MulAut ↥S.Uv)) : Subgroup G :=
  ((Q.comap (conjAct S.Uv)).map (Subgroup.normalizer (S.Uv : Set G)).subtype) ⊓
    Subgroup.centralizer ({S.v12} : Set G)

theorem mem_preGv {Q : Subgroup (MulAut ↥S.Uv)} {g : G} :
    g ∈ S.preGv Q ↔ ∃ hg : g ∈ Subgroup.centralizer ({S.v12} : Set G),
      conjAct S.Uv ⟨g, S.Gv_le_normalizer_Uv hg⟩ ∈ Q := by
  constructor
  · rintro ⟨⟨⟨y, hyN⟩, hy, rfl⟩, hg⟩
    exact ⟨hg, hy⟩
  · rintro ⟨hg, hq⟩
    exact ⟨⟨⟨g, S.Gv_le_normalizer_Uv hg⟩, hq, rfl⟩, hg⟩

theorem exists_normalizer_thompsonJ (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) {x : MulAut ↥S.Uv}
    (hxG : x ∈ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv)
    (hxN : x ∈ Subgroup.normalizer ((autOn S.Tv S.Uv ⊓ S.JGv : Subgroup (MulAut ↥S.Uv)) :
      Set (MulAut ↥S.Uv))) :
    ∃ (y : G) (hy : y ∈ Subgroup.centralizer ({S.v12} : Set G)),
      y ∈ Subgroup.normalizer (thompsonJ S.Tv : Set G) ∧
      ∃ r ∈ autOn S.Tv S.Uv ⊓ S.JGv, conjAct S.Uv ⟨y, S.Gv_le_normalizer_Uv hy⟩ = r * x := by
  set Q : Subgroup (MulAut ↥S.Uv) := autOn S.Tv S.Uv ⊓ S.JGv with hQ
  set Y := S.preGv (Subgroup.normalizer (Q : Set (MulAut ↥S.Uv))) with hY
  set X := S.preGv Q with hX
  have hsyl := S.isSylowTwoOf_Tv h1222 h517
  have hGU := S.Gv_le_normalizer_Uv
  have hXY : X ≤ Y := fun g hg => by
    obtain ⟨hg, hq⟩ := S.mem_preGv.1 hg
    exact S.mem_preGv.2 ⟨hg, Subgroup.le_normalizer hq⟩
  have hYX : Y ≤ Subgroup.normalizer (X : Set G) := by
    have key : ∀ k ∈ Y, ∀ g ∈ X, k * g * k⁻¹ ∈ X := by
      intro k hk g hg
      obtain ⟨hkG, hkq⟩ := S.mem_preGv.1 hk
      obtain ⟨hgG, hgq⟩ := S.mem_preGv.1 hg
      have hm : k * g * k⁻¹ ∈ Subgroup.centralizer ({S.v12} : Set G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hkG hgG) (Subgroup.inv_mem _ hkG)
      refine S.mem_preGv.2 ⟨hm, ?_⟩
      rw [show (⟨k * g * k⁻¹, hGU hm⟩ : ↥(Subgroup.normalizer (S.Uv : Set G))) =
        ⟨k, hGU hkG⟩ * ⟨g, hGU hgG⟩ * (⟨k, hGU hkG⟩)⁻¹ from rfl, map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hkq _).mp hgq
    intro y hy
    refine B6.mem_normalizer_of_forall_mem (key y hy) fun g hg => ?_
    have := key y⁻¹ (Y.inv_mem hy) g hg
    rwa [inv_inv] at this
  have hTY : S.Tv ≤ Y := by
    intro t ht
    have htG := S.Tv_le_Gv ht
    refine S.mem_preGv.2 ⟨htG, ?_⟩
    have hts : conjAct S.Uv ⟨t, hGU htG⟩ ∈ autOn S.Tv S.Uv :=
      Setup.mem_autOn_iff.2 ⟨⟨t, hGU htG⟩, ht, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro q
    rw [hQ, Subgroup.mem_inf, Subgroup.mem_inf,
      (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hts) q),
      (Subgroup.mem_normalizer_iff.mp (S.GvS_le_normalizer_JGv (S.autOn_le_GvS S.Tv_le_Gv hts))
        q)]
  have hTY' : IsSylowTwoOf S.Tv Y := B6.isSylowTwoOf_mono hsyl hTY inf_le_right
  have hJX : thompsonJ S.Tv ≤ X := by
    intro j hj
    have hjT : j ∈ S.Tv := B6.thompsonJ_le S.Tv hj
    have hjG := S.Tv_le_Gv hjT
    refine S.mem_preGv.2 ⟨hjG, ?_, ?_⟩
    · exact Setup.mem_autOn_iff.2 ⟨⟨j, hGU hjG⟩, hjT, rfl⟩
    · exact S.autOn_thompsonJ_le_JGv (Setup.mem_autOn_iff.2 ⟨⟨j, hGU hjG⟩, hj, rfl⟩)
  have hTX : IsSylowTwoOf (S.Tv ⊓ X) X := B6.isSylowTwoOf_inf_normal hTY' hXY hYX
  obtain ⟨⟨g, hgN⟩, hgG, rfl⟩ := Setup.mem_autOn_iff.1 hxG
  have hgY : g ∈ Y := S.mem_preGv.2 ⟨hgG, hxN⟩
  obtain ⟨n, hnX, k, ⟨hkY, hkN⟩, hgnk⟩ := exists_mul_normalizer_of_sylow hXY hYX hTX hgY
  have hJ : thompsonJ (S.Tv ⊓ X) = thompsonJ S.Tv :=
    B6.thompsonJ_eq_of_le (le_inf (B6.thompsonJ_le S.Tv) hJX) inf_le_left
  have hkJ : k ∈ Subgroup.normalizer (thompsonJ S.Tv : Set G) := by
    rw [← hJ]
    exact normalizer_le_normalizer_thompsonJ _ hkN
  obtain ⟨hkG, -⟩ := S.mem_preGv.1 hkY
  obtain ⟨hnG, hnq⟩ := S.mem_preGv.1 hnX
  refine ⟨k, hkG, hkJ, (conjAct S.Uv ⟨n, hGU hnG⟩)⁻¹, Q.inv_mem hnq, ?_⟩
  have e : (⟨k, hGU hkG⟩ : ↥(Subgroup.normalizer (S.Uv : Set G))) =
      (⟨n, hGU hnG⟩)⁻¹ * ⟨g, hgN⟩ := Subtype.ext (by
    show k = n⁻¹ * g
    rw [hgnk, inv_mul_cancel_left])
  rw [e, map_mul, map_inv]

theorem exists_normalizer_baum (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) {y : G} (hyG : y ∈ Subgroup.centralizer ({S.v12} : Set G))
    (hyJ : y ∈ Subgroup.normalizer (thompsonJ S.Tv : Set G)) :
    ∃ c ∈ Subgroup.centralizer (omegaOneCenterOf (thompsonJ S.Tv) : Set G),
      ∃ k ∈ Subgroup.centralizer ({S.v12} : Set G) ⊓ Subgroup.normalizer (baum S.Tv : Set G),
        y = c * k := by
  set E := omegaOneCenterOf (thompsonJ S.Tv) with hE
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  set H := Gv ⊓ Subgroup.normalizer (E : Set G) with hH
  set N := Gv ⊓ Subgroup.centralizer (E : Set G) with hN
  have hNH : N ≤ H := inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := by
    have key : ∀ h ∈ H, ∀ x ∈ N, h * x * h⁻¹ ∈ N := by
      intro h hh x hx
      refine Subgroup.mem_inf.mpr
        ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hh.1 hx.1) (Subgroup.inv_mem _ hh.1), ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have he' : h⁻¹ * e * h ∈ E := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hh.2) e).mp he
        simpa using this
      have hc := Subgroup.mem_centralizer_iff.mp hx.2 _ he'
      calc e * (h * x * h⁻¹) = h * ((h⁻¹ * e * h) * x) * h⁻¹ := by group
        _ = h * (x * (h⁻¹ * e * h)) * h⁻¹ := by rw [hc]
        _ = h * x * h⁻¹ * e := by group
    intro h hh
    refine B6.mem_normalizer_of_forall_mem (key h hh) fun x hx => ?_
    have := key h⁻¹ (H.inv_mem hh) x hx
    rwa [inv_inv] at this
  have hTH : S.Tv ≤ H := le_inf S.Tv_le_Gv
    ((B6.le_normalizer_thompsonJ S.Tv).trans (A4.normalizer_le_normalizer_omegaOneCenterOf _))
  have hTH' : IsSylowTwoOf S.Tv H :=
    B6.isSylowTwoOf_mono (S.isSylowTwoOf_Tv h1222 h517) hTH inf_le_left
  have hTN := B6.isSylowTwoOf_inf_normal hTH' hNH hHN
  have hyH : y ∈ H := ⟨hyG, A4.normalizer_le_normalizer_omegaOneCenterOf _ hyJ⟩
  obtain ⟨c, hcN, k, ⟨hkH, hkS⟩, rfl⟩ := exists_mul_normalizer_of_sylow hNH hHN hTN hyH
  have hTv : S.Tv ⊓ N = baum S.Tv := by
    rw [hN, baum, ← inf_assoc, inf_eq_left.mpr S.Tv_le_Gv]
  rw [hTv] at hkS
  exact ⟨c, hcN.2, k, ⟨hkH.1, hkS⟩, rfl⟩

theorem forall_Uv_of_zU [IsMulCommutative ↥S.Uv] {J : Subgroup (MulAut ↥S.Uv)}
    (hJ : autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv ≤
      Subgroup.normalizer (J : Set (MulAut ↥S.Uv)))
    (h : ∀ j ∈ J, j S.zU * S.zU⁻¹ ∈ fixV J) : ∀ j ∈ J, ∀ u : ↥S.Uv, j u * u⁻¹ ∈ fixV J := by
  let M : Subgroup ↥S.Uv :=
    { carrier := {u | ∀ j ∈ J, j u * u⁻¹ ∈ fixV J}
      one_mem' := fun j _ => by simp [(fixV J).one_mem]
      mul_mem' := fun {a b} ha hb j hj => by
        have e : j (a * b) * (a * b)⁻¹ = (j a * a⁻¹) * (j b * b⁻¹) := by
          simp only [map_mul, mul_inv_rev]
          ac_rfl
        rw [e]
        exact (fixV J).mul_mem (ha j hj) (hb j hj)
      inv_mem' := fun {a} ha j hj => by
        have e : j a⁻¹ * a⁻¹⁻¹ = (j a * a⁻¹)⁻¹ := by
          simp only [map_inv, inv_inv, mul_inv_rev]
          ac_rfl
        rw [e]
        exact (fixV J).inv_mem (ha j hj) }
  have hconj : ∀ (g : G) (hg : g ∈ Subgroup.centralizer ({S.v12} : Set G)),
      conjAct S.Uv ⟨g, S.Gv_le_normalizer_Uv hg⟩ S.zU ∈ M := by
    intro g hg j hj
    set a := conjAct S.Uv ⟨g, S.Gv_le_normalizer_Uv hg⟩ with ha
    have haG : a ∈ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv :=
      Setup.mem_autOn_iff.2 ⟨⟨g, S.Gv_le_normalizer_Uv hg⟩, hg, rfl⟩
    have hconjJ : ∀ k ∈ J, a⁻¹ * k * a ∈ J := by
      intro k hk
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hJ haG)) k).mp hk
      simpa using this
    have haC : ∀ c ∈ fixV J, a c ∈ fixV J := by
      intro c hc k hk
      calc k (a c) = a ((a⁻¹ * k * a) c) := by
            rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
        _ = a c := by rw [(mem_fixV.mp hc) _ (hconjJ k hk)]
    have e : a ((a⁻¹ * j * a) S.zU * S.zU⁻¹) = j (a S.zU) * (a S.zU)⁻¹ := by
      rw [map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
    rw [← e]
    exact haC _ (h _ (hconjJ j hj))
  have hle : S.Uv ≤ M.map S.Uv.subtype := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨g, hg, z', hz', rfl⟩
    rcases S.mem_V1.1 hz' with rfl | rfl
    · simp
    · exact ⟨_, hconj g hg, by rw [Subgroup.coe_subtype, InternalSec.coe_conjAct_apply]; rfl⟩
  intro j hj u
  obtain ⟨m, hm, hmu⟩ := hle u.2
  have : m = u := Subtype.ext hmu
  rw [← this]
  exact hm j hj

end Setting

end CFSG.Quasithin.H13.A5
