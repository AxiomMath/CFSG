module

public import CFSG.Quasithin.H13.A5S136e
public import CFSG.Quasithin.Background.F8G2

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

@[expose] def c234 : Equiv.Perm (Fin 5) := Equiv.swap 2 3 * Equiv.swap 3 4

theorem c234_sign : c234.sign = 1 := by decide

theorem pb_sign : pb.sign = 1 := by decide

theorem pact_c234_E12 : pact c234 E12 = E12 := by decide +kernel

theorem c234_pow_two_pow (k : ℕ) : c234 ^ 2 ^ k = c234 ∨ c234 ^ 2 ^ k = c234⁻¹ := by
  induction k with
  | zero => left; simp
  | succ k ih =>
    rw [pow_succ, pow_mul]
    rcases ih with h | h <;> rw [h]
    · right; decide
    · left; decide

theorem c01_ker_gen : ∀ x : W5, c01 x = 1 →
    x ∈ [1, W4, pact c234 W4, W4 * pact c234 W4, pact c234⁻¹ W4, W4 * pact c234⁻¹ W4,
      pact c234 W4 * pact c234⁻¹ W4, W4 * pact c234 W4 * pact c234⁻¹ W4] := by
  decide +kernel

theorem W5_eq_mul_pb : ∀ w : W5, ∃ b : W5, c01 b = 1 ∧ c01 (w * (pact pb b)⁻¹) = 1 := by
  decide +kernel

theorem c01_pact_of_fix : ∀ (σ : Equiv.Perm (Fin 5)) (x : W5), pact σ E12 = E12 → c01 x = 1 →
    c01 (pact σ x) = 1 := by
  decide +kernel

theorem c01_W4 : c01 W4 = 1 := by decide +kernel

theorem c01_pb_E12 : c01 (pact pb E12) = 1 := by decide +kernel

theorem pb_E12_ne_one : pact pb E12 ≠ 1 := by decide +kernel

theorem not_isSing_pb_E12 : ¬ IsSing (pact pb E12) := by decide +kernel

theorem E12_ne_W4 : E12 ≠ W4 := by decide +kernel

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

@[expose] noncomputable def Vv : Subgroup G := S.pre c01.ker

@[expose] noncomputable def Lv : Subgroup G :=
  oTwoRes (L ⊓ Subgroup.centralizer ({S.v12} : Set G))

@[expose] noncomputable def Uv : Subgroup G :=
  conjClosure S.V1 (Subgroup.centralizer ({S.v12} : Set G))

theorem mem_Vv {x : G} : x ∈ S.Vv ↔ ∃ h : x ∈ V, c01 (S.frame.ψ ⟨x, h⟩) = 1 := by
  rw [Vv, S.mem_pre]
  rfl

theorem Vv_le_V : S.Vv ≤ V := S.pre_le_V _

theorem z_mem_Vv : S.z ∈ S.Vv := S.mem_Vv.2 ⟨S.z_mem_V, by rw [S.psi_z]; exact c01_W4⟩

theorem v12_not_mem_V1 : S.v12 ∉ S.V1 := by
  intro h
  rcases S.mem_V1.1 h with h1 | h1
  · have : (⟨S.v12, S.v12_mem_V⟩ : ↥V) = 1 := Subtype.ext h1
    have h2 := S.psi_v12
    rw [this, map_one] at h2
    exact E12_ne_one h2.symm
  · have : (⟨S.v12, S.v12_mem_V⟩ : ↥V) = ⟨S.z, S.z_mem_V⟩ := Subtype.ext h1
    have h2 := S.psi_v12
    rw [this, S.psi_z] at h2
    exact E12_ne_W4 h2.symm

theorem mem_centralizer_v12 (g : ↥(Subgroup.normalizer (V : Set G)))
    (hg : pact (S.frame.ρ g) E12 = E12) :
    (g : G) ∈ Subgroup.centralizer ({S.v12} : Set G) := by
  have h := (S.conj_eq_iff g ⟨S.v12, S.v12_mem_V⟩).2 (by rw [S.psi_v12]; exact hg)
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc (g : G) * S.v12 = (g : G) * S.v12 * (g : G)⁻¹ * g := by group
    _ = S.v12 * g := by rw [h]

theorem conj_mem_Vv {g : G} (hgN : g ∈ Subgroup.normalizer (V : Set G))
    (hgv : g ∈ Subgroup.centralizer ({S.v12} : Set G)) {x : G} (hx : x ∈ S.Vv) :
    g * x * g⁻¹ ∈ S.Vv := by
  obtain ⟨hxV, hc⟩ := S.mem_Vv.1 hx
  have hfix : pact (S.frame.ρ ⟨g, hgN⟩) E12 = E12 := by
    have h1 : g * S.v12 * g⁻¹ = S.v12 := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hgv
      rw [hgv]
      group
    have h2 := (S.conj_eq_iff ⟨g, hgN⟩ ⟨S.v12, S.v12_mem_V⟩).1 h1
    rwa [S.psi_v12] at h2
  refine S.mem_Vv.2 ⟨(Subgroup.mem_normalizer_iff.mp hgN x).mp hxV, ?_⟩
  have h3 := S.psi_conj ⟨g, hgN⟩ ⟨x, hxV⟩
  simp only at h3
  rw [h3]
  exact c01_pact_of_fix _ _ hfix hc

theorem normalizer_inf_le_normalizer_Vv :
    Subgroup.normalizer (V : Set G) ⊓ Subgroup.centralizer ({S.v12} : Set G) ≤
      Subgroup.normalizer (S.Vv : Set G) := by
  intro g hg
  obtain ⟨hgN, hgv⟩ := Subgroup.mem_inf.mp hg
  refine B6.mem_normalizer_of_forall_mem (fun x hx => S.conj_mem_Vv hgN hgv hx) fun x hx => ?_
  simpa using S.conj_mem_Vv (Subgroup.inv_mem _ hgN) (Subgroup.inv_mem _ hgv) hx

theorem Vv_le_of_gen {Y : Subgroup G} (l : ↥(Subgroup.normalizer (V : Set G)))
    (hl : S.frame.ρ l = c234 ∨ S.frame.ρ l = c234⁻¹) (hz : S.z ∈ Y)
    (h1 : (l : G) * S.z * (l : G)⁻¹ ∈ Y) (h2 : (l : G)⁻¹ * S.z * (l : G) ∈ Y) : S.Vv ≤ Y := by
  set P : Subgroup W5 := (Y.subgroupOf V).map S.frame.ψ.toMonoidHom with hP
  have hmemP : ∀ u : ↥V, (u : G) ∈ Y → S.frame.ψ u ∈ P := fun u hu =>
    ⟨u, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
  have hW4 : W4 ∈ P := by
    rw [← S.psi_z]
    exact hmemP _ hz
  have hA : pact (S.frame.ρ l) W4 ∈ P := by
    rw [← S.psi_z, ← S.psi_conj l]
    exact hmemP _ h1
  have hB : pact (S.frame.ρ l⁻¹) W4 ∈ P := by
    rw [← S.psi_z, ← S.psi_conj l⁻¹]
    refine hmemP _ ?_
    simpa using h2
  rw [map_inv] at hB
  have hAB : pact c234 W4 ∈ P ∧ pact c234⁻¹ W4 ∈ P := by
    rcases hl with hl | hl
    · rw [hl] at hA hB
      exact ⟨hA, hB⟩
    · rw [hl, inv_inv] at hB
      rw [hl] at hA
      exact ⟨hB, hA⟩
  obtain ⟨hA', hB'⟩ := hAB
  have hgen : ∀ x : W5, c01 x = 1 → x ∈ P := by
    intro x hx
    have hc := c01_ker_gen x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact P.one_mem
    · exact hW4
    · exact hA'
    · exact P.mul_mem hW4 hA'
    · exact hB'
    · exact P.mul_mem hW4 hB'
    · exact P.mul_mem hA' hB'
    · exact P.mul_mem (P.mul_mem hW4 hA') hB'
  intro x hx
  obtain ⟨hxV, hc⟩ := S.mem_Vv.1 hx
  obtain ⟨u, hu, hux⟩ := hgen _ hc
  have hu' : u = ⟨x, hxV⟩ := S.frame.ψ.injective hux
  rw [hu'] at hu
  exact Subgroup.mem_subgroupOf.mp hu

theorem Vv_eq_conjClosure : S.Vv = conjClosure S.V1 S.Lv := by
  have hLv : S.Lv ≤ L ⊓ Subgroup.centralizer ({S.v12} : Set G) := by
    rw [Lv, oTwoRes_eq_oTwoUpper]
    exact oTwoUpper_le _
  apply le_antisymm
  · obtain ⟨l₀, hl₀L, hl₀σ⟩ := (S.frame.image_L c234).2 c234_sign
    have hl₀ : (l₀ : G) ∈ L ⊓ Subgroup.centralizer ({S.v12} : Set G) :=
      ⟨hl₀L, S.mem_centralizer_v12 l₀ (by rw [hl₀σ]; exact pact_c234_E12)⟩
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper _ hl₀
    rw [← oTwoRes_eq_oTwoUpper] at hk
    have hk' : (l₀ : G) ^ 2 ^ k ∈ S.Lv := hk
    have hz : S.z ∈ S.V1 := Subgroup.mem_zpowers _
    refine S.Vv_le_of_gen (l₀ ^ 2 ^ k) ?_ (le_conjClosure _ _ hz) ?_ ?_
    · rw [map_pow, hl₀σ]
      exact c234_pow_two_pow k
    · exact mem_conjClosure (by simpa using hk') hz
    · simpa using mem_conjClosure ((S.Lv).inv_mem (by simpa using hk')) hz
  · refine conjClosure_le fun h hh x hx => ?_
    obtain ⟨hhL, hhv⟩ := Subgroup.mem_inf.mp (hLv hh)
    have hxz : x ∈ S.Vv := by
      rcases S.mem_V1.1 hx with rfl | rfl
      · exact S.Vv.one_mem
      · exact S.z_mem_Vv
    exact S.conj_mem_Vv (S.frame.L_le hhL) hhv hxz

theorem Vv_le_Uv : S.Vv ≤ S.Uv := by
  rw [Vv_eq_conjClosure]
  refine conjClosure_mono le_rfl ?_
  rw [Lv, oTwoRes_eq_oTwoUpper]
  exact (oTwoUpper_le _).trans inf_le_right

theorem le_normalizer_V_of_Vv (h1326 : Input1326Two)
    (h : Subgroup.centralizer ({S.v12} : Set G) ≤ Subgroup.normalizer (S.Vv : Set G)) :
    Subgroup.centralizer ({S.v12} : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  obtain ⟨l, -, hlσ⟩ := (S.frame.image_L pb).2 pb_sign
  have key : ∀ g ∈ Subgroup.centralizer ({S.v12} : Set G), ∀ x ∈ V, g * x * g⁻¹ ∈ V := by
    intro g hg x hx
    have hgN := h hg
    have huV : (l : G) * S.v12 * (l : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp l.2 _).mp S.v12_mem_V
    have hψu : S.frame.ψ ⟨(l : G) * S.v12 * (l : G)⁻¹, huV⟩ = pact pb E12 := by
      rw [S.psi_conj l ⟨S.v12, S.v12_mem_V⟩, hlσ, S.psi_v12]
    have huVv : (l : G) * S.v12 * (l : G)⁻¹ ∈ S.Vv :=
      S.mem_Vv.2 ⟨huV, by rw [hψu]; exact c01_pb_E12⟩
    have hwVv : g * ((l : G) * S.v12 * (l : G)⁻¹) * g⁻¹ ∈ S.Vv :=
      (Subgroup.mem_normalizer_iff.mp hgN _).mp huVv
    have hwV := S.Vv_le_V hwVv
    have hws : ¬ IsSing (S.frame.ψ ⟨_, hwV⟩) := by
      rw [← h1326 G T L V S g ⟨_, huV⟩ ⟨_, hwV⟩ rfl, hψu]
      exact not_isSing_pb_E12
    have hw1 : S.frame.ψ ⟨_, hwV⟩ ≠ 1 := by
      intro h1
      have h2 : g * ((l : G) * S.v12 * (l : G)⁻¹) * g⁻¹ = 1 :=
        congrArg Subtype.val (S.frame.ψ.injective (h1.trans (map_one _).symm))
      have h3 : (l : G) * S.v12 * (l : G)⁻¹ = 1 := by
        have : (l : G) * S.v12 * (l : G)⁻¹ = g⁻¹ * (g * ((l : G) * S.v12 * (l : G)⁻¹) * g⁻¹) * g :=
          by group
        rw [this, h2]
        group
      have h4 : (⟨_, huV⟩ : ↥V) = 1 := Subtype.ext h3
      rw [h4, map_one] at hψu
      exact pb_E12_ne_one hψu.symm
    obtain ⟨σ', hσ', hσ'w⟩ := exists_alt_pact E12 _ E12_ne_one hw1
      (iff_of_false not_isSing_E12 hws)
    obtain ⟨l', -, hl'σ'⟩ := (S.frame.image_L σ').2 hσ'
    have hl'w : (l' : G) * S.v12 * (l' : G)⁻¹ = g * ((l : G) * S.v12 * (l : G)⁻¹) * g⁻¹ := by
      have hc := S.psi_conj l' ⟨S.v12, S.v12_mem_V⟩
      rw [hl'σ', S.psi_v12, hσ'w] at hc
      exact congrArg Subtype.val (S.frame.ψ.injective hc)
    have hk : (l' : G)⁻¹ * g * l ∈ Subgroup.centralizer ({S.v12} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have e1 : (l' : G)⁻¹ * g * l * S.v12 =
          (l' : G)⁻¹ * (g * ((l : G) * S.v12 * (l : G)⁻¹) * g⁻¹) * (g * l) := by group
      rw [e1, ← hl'w]
      group
    have hkN := h hk
    obtain ⟨b, hb, hab⟩ := W5_eq_mul_pb (S.frame.ψ ⟨x, hx⟩)
    set a : W5 := S.frame.ψ ⟨x, hx⟩ * (pact pb b)⁻¹ with ha
    have ha₀ : ((S.frame.ψ.symm a : ↥V) : G) ∈ S.Vv :=
      S.mem_Vv.2 ⟨(S.frame.ψ.symm a).2, by simpa using hab⟩
    have hb₀ : ((S.frame.ψ.symm b : ↥V) : G) ∈ S.Vv :=
      S.mem_Vv.2 ⟨(S.frame.ψ.symm b).2, by simpa using hb⟩
    have hlb : (l : G) * (S.frame.ψ.symm b : ↥V) * (l : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp l.2 _).mp (S.frame.ψ.symm b).2
    have hx_eq : x = ((S.frame.ψ.symm a : ↥V) : G) *
        ((l : G) * (S.frame.ψ.symm b : ↥V) * (l : G)⁻¹) := by
      have e : (⟨x, hx⟩ : ↥V) = S.frame.ψ.symm a * ⟨_, hlb⟩ := by
        apply S.frame.ψ.injective
        rw [map_mul, S.psi_conj l (S.frame.ψ.symm b), hlσ, MulEquiv.apply_symm_apply,
          MulEquiv.apply_symm_apply, ha, inv_mul_cancel_right]
      exact congrArg Subtype.val e
    rw [hx_eq]
    have e2 : g * (((S.frame.ψ.symm a : ↥V) : G) *
        ((l : G) * (S.frame.ψ.symm b : ↥V) * (l : G)⁻¹)) * g⁻¹ =
        (g * (S.frame.ψ.symm a : ↥V) * g⁻¹) * ((l' : G) * (((l' : G)⁻¹ * g * l) *
          (S.frame.ψ.symm b : ↥V) * ((l' : G)⁻¹ * g * l)⁻¹) * (l' : G)⁻¹) := by group
    rw [e2]
    refine V.mul_mem (S.Vv_le_V ((Subgroup.mem_normalizer_iff.mp hgN _).mp ha₀)) ?_
    have h5 : ((l' : G)⁻¹ * g * l) * (S.frame.ψ.symm b : ↥V) * ((l' : G)⁻¹ * g * l)⁻¹ ∈ V :=
      S.Vv_le_V ((Subgroup.mem_normalizer_iff.mp hkN _).mp hb₀)
    exact (Subgroup.mem_normalizer_iff.mp l'.2 _).mp h5
  intro g hg
  refine B6.mem_normalizer_of_forall_mem (key g hg) fun x hx => ?_
  simpa using key g⁻¹ (Subgroup.inv_mem _ hg) x hx

theorem le_normalizer_Vv_of_thompsonJ (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    (hJ : thompsonJ (T ⊓ Subgroup.centralizer ({S.v12} : Set G)) ≤
      Subgroup.centralizer (S.Uv : Set G)) :
    Subgroup.centralizer ({S.v12} : Set G) ≤ Subgroup.normalizer (S.Vv : Set G) := by
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  have hsyl : IsSylowTwoOf (T ⊓ Gv) Gv :=
    S.isSylowTwoOf_centralizer h1222 h517 S.v12_mem_V2 S.v12_not_mem_V1
  have hzGv : S.z ∈ Gv := by
    rw [hGv, Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val
      (S.elemAbelian_V.1.is_comm.comm ⟨S.z, S.z_mem_V⟩ ⟨S.v12, S.v12_mem_V⟩)
  have hzC : S.z ∈ Subgroup.centralizer ((T ⊓ Gv : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have := S.conj_z_of_mem_T (Subgroup.mem_inf.mp ht).1
    calc t * S.z = t * S.z * t⁻¹ * t := by group
      _ = S.z * t := by rw [this]
  have hZ : S.V1 ≤ quasithinOmegaOneCenter (T ⊓ Gv) := by
    rw [V1, Subgroup.zpowers_le]
    exact Subgroup.subset_closure
      ⟨Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨S.V_le_T S.z_mem_V, hzGv⟩, hzC⟩, S.z_sq⟩
  obtain ⟨hUc, hUe⟩ :=
    conjClosure_le_centerOf_pCoreOf_of_sylowIn hsyl.1 hsyl.2.1 hsyl.2.2 hF hZ
  replace hUc : S.Uv ≤ centerOf (pCoreOf 2 Gv) := hUc
  replace hUe : IsElemAbelian 2 S.Uv := hUe
  have hUN : Gv ≤ Subgroup.normalizer (S.Uv : Set G) := le_normalizer_conjClosure S.V1 Gv
  have hUT : S.Uv ≤ T ⊓ Gv :=
    hUc.trans (inf_le_left.trans (pCoreOf_two_le_of_isSylowTwoOf hsyl))
  have hb : baum T = baum ((T ⊓ Gv) ⊓ Subgroup.centralizer (S.Uv : Set G)) := by
    rw [← baum_eq_baum_centralizer hUe hUT (le_inf (B6.thompsonJ_le _) hJ)]
    exact S.lemma_13_6_4.1.symm
  have hNG : Gv ⊓ Subgroup.centralizer (S.Uv : Set G) ≤ Gv := inf_le_left
  have hcent : ∀ g ∈ Gv, ∀ x ∈ Subgroup.centralizer (S.Uv : Set G),
      g * x * g⁻¹ ∈ Subgroup.centralizer (S.Uv : Set G) := by
    intro g hg x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro u hu
    have hu' : g⁻¹ * u * g ∈ S.Uv := by
      have := (Subgroup.mem_normalizer_iff.mp (hUN (Gv.inv_mem hg)) u).mp hu
      simpa using this
    have h1 := hx _ hu'
    calc u * (g * x * g⁻¹) = g * ((g⁻¹ * u * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * u * g)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * u := by group
  have hGN : Gv ≤ Subgroup.normalizer
      ((Gv ⊓ Subgroup.centralizer (S.Uv : Set G) : Subgroup G) : Set G) := by
    intro g hg
    refine B6.mem_normalizer_of_forall_mem (fun x hx => ?_) fun x hx => ?_
    · exact ⟨Gv.mul_mem (Gv.mul_mem hg hx.1) (Gv.inv_mem hg), hcent g hg x hx.2⟩
    · have h1 := hcent g⁻¹ (Gv.inv_mem hg) x hx.2
      rw [inv_inv] at h1
      exact ⟨Gv.mul_mem (Gv.mul_mem (Gv.inv_mem hg) hx.1) hg, h1⟩
  have hsylN := A4.isSylowTwoOf_inf_normal hsyl hNG hGN
  have hTN : (T ⊓ Gv) ⊓ (Gv ⊓ Subgroup.centralizer (S.Uv : Set G)) =
      (T ⊓ Gv) ⊓ Subgroup.centralizer (S.Uv : Set G) := by
    rw [← inf_assoc, inf_assoc T Gv Gv, inf_idem]
  refine (B6.frattini_two hNG hGN hsylN).trans (sup_le ?_ ?_)
  ·
    intro x hx
    have hxc : x ∈ Subgroup.centralizer (S.Vv : Set G) :=
      Subgroup.centralizer_le S.Vv_le_Uv (Subgroup.mem_inf.mp hx).2
    exact Subgroup.centralizer_le_normalizer _ hxc
  ·
    intro x hx
    obtain ⟨hxG, hxN⟩ := Subgroup.mem_inf.mp hx
    rw [hTN] at hxN
    have hxb : x ∈ Subgroup.normalizer (baum T : Set G) := by
      rw [hb]
      exact normalizer_le_normalizer_baum _ hxN
    exact S.normalizer_inf_le_normalizer_Vv (S.lemma_13_6_5 h1222 h517 ⟨hxG, hxb⟩)

end Setting

@[expose] def Lemma1366 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V),
    IsElemAbelian 2 (conjClosure V S.G1) → CharTwo (Subgroup.centralizer ({S.v12} : Set G))

@[expose] def Main1367 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V),
    IsElemAbelian 2 (conjClosure V S.G1) →
    CharTwo (Subgroup.centralizer ({S.v12} : Set G)) →
    ¬ Subgroup.centralizer ({S.v12} : Set G) ≤ Subgroup.normalizer (S.Vv : Set G) →
    ¬ thompsonJ (T ⊓ Subgroup.centralizer ({S.v12} : Set G)) ≤
      Subgroup.centralizer (S.Uv : Set G) →
      False

theorem thm13_6_7_of (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one)
    (h1366 : Lemma1366) (hmain : Main1367) : Thm13_6_7 := by
  intro G _ _ T L V S hab
  have hF := h1366 G T L V S hab
  refine S.le_normalizer_V_of_Vv (input1326Two_of h1222 h517) ?_
  by_contra hVv
  exact hmain G T L V S hab hF hVv fun hJ =>
    hVv (S.le_normalizer_Vv_of_thompsonJ h1222 h517 hF hJ)

end CFSG.Quasithin.H13.A5
