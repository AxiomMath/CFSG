module

public import CFSG.Quasithin.H13.L32NLem14333m
public import CFSG.RankThree.PartTwo.Sec8.TransferExtremal

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint L14332 CFSG.LieType.BorelTits CFSG.Quasithin.SL3Model
open scoped commutatorElement MatrixGroups

namespace L14333

variable {G : Type} [Group G] [Finite G]

namespace Inv

variable {T L V V₂ K : Subgroup G} {g a z b d x r : G} {D : HatModelU (fsuU T V)}
  (ι : Inv G T L V V₂ K g a z b d x r D)
include ι

theorem conj_not_mem_L {g : G}
    (hg : ∀ y ∈ T ⊓ Subgroup.centralizer ({r} : Set G), g⁻¹ * y * g ∈ T) :
    g⁻¹ * r * g ∉ L := by
  obtain ⟨_, S⟩ := ι.setting
  intro hyL
  have hyT : g⁻¹ * r * g ∈ T := hg r ⟨ι.r_T, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  set y := g⁻¹ * r * g with hy
  have hy2 : y * y = 1 := by
    calc y * y = g⁻¹ * (r * r) * g := by rw [hy]; group
      _ = 1 := by rw [ι.r_sq]; group
  have hyV : y ∉ V := ι.not_conj_V g
  have hyP : y ∉ pCoreOf 2 L := fun h => hyV (ι.mem_V_of_mul_self ι.hyp h hy2)
  have hyU : y ∉ fsuU T V := by
    intro hyU
    have hyZ : y ∉ centerOf (fsuU T V) := fun h =>
      hyP ((le_sup_right.trans (ι.sup_zU_le_P ι.hyp)) h)
    obtain ⟨h, -, hhv⟩ := ι.exists_conj_V_of_mem_U ι.hyp hyU hy2 hyZ
    apply ι.not_conj_V (g * h)
    have e : (g * h)⁻¹ * r * (g * h) = h⁻¹ * y * h := by rw [hy]; group
    rw [e]
    exact hhv
  obtain ⟨hle, hsq⟩ := ι.card_cent_le hyT hyL hy2 hyP hyU
  set X := T ⊓ Subgroup.centralizer ({r} : Set G) with hX
  set C := T ⊓ Subgroup.centralizer ({y} : Set G) with hC
  set Xg := X.map (MulAut.conj g⁻¹).toMonoidHom with hXg'
  have hconj : ∀ t : G, (MulAut.conj g⁻¹).toMonoidHom t = g⁻¹ * t * g := fun t => by
    simp
  have hXg : Xg ≤ C := by
    rintro _ ⟨t, ht, rfl⟩
    rw [hconj]
    refine ⟨hg t ht, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have htr : t * r = r * t := Subgroup.mem_centralizer_singleton_iff.mp ht.2
    calc g⁻¹ * t * g * y = g⁻¹ * (t * r) * g := by rw [hy]; group
      _ = g⁻¹ * (r * t) * g := by rw [htr]
      _ = y * (g⁻¹ * t * g) := by rw [hy]; group
  have hXgc : Nat.card ↥Xg = Nat.card ↥X :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hXc : 2 ^ 7 ≤ Nat.card ↥X := ι.card_X_ge
  have hCc := Subgroup.card_le_of_le hXg
  have hCeq : Xg = C := Subgroup.eq_of_le_of_card_ge hXg (by omega)
  obtain ⟨s, hsC, hss⟩ := hsq (by omega)
  have hzC : z ∈ C := ⟨ι.U_le_T (ι.ctx.V_U ι.z_mem_V),
    Subgroup.mem_centralizer_singleton_iff.mpr (ι.z_comm hyT).symm⟩
  rw [← hCeq] at hsC hzC
  obtain ⟨s', hs'X, rfl⟩ := hsC
  obtain ⟨w, hwX, hwz⟩ := hzC
  rw [hconj] at hss hwz
  have hw : w = s' * s' := by
    calc w = g * (g⁻¹ * w * g) * g⁻¹ := by group
      _ = g * (g⁻¹ * s' * g * (g⁻¹ * s' * g)) * g⁻¹ := by rw [hwz, hss]
      _ = s' * s' := by group
  have hwc : ∀ t ∈ X, t * (s' * s') = s' * s' * t := by
    intro t ht
    have h1 : g⁻¹ * t * g ∈ T := hg t ht
    have h2 := ι.z_comm h1
    rw [← hwz] at h2
    rw [← hw]
    calc t * w = g * (g⁻¹ * t * g * (g⁻¹ * w * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * w * g * (g⁻¹ * t * g)) * g⁻¹ := by rw [h2]
      _ = w * t := by group
  rcases ι.eq_of_mem_V1 (ι.sq_mem_V1 hs'X hwc) with h1 | h1
  · apply ι.z_ne
    rw [← hwz, hw, h1]
    group
  · have hgz : g * z * g⁻¹ = z := by
      calc g * z * g⁻¹ = g * (g⁻¹ * w * g) * g⁻¹ := by rw [hwz]
        _ = w := by group
        _ = z := by rw [hw, h1]
    have hgH : g ∈ l32nH T V := S.mem_g1 ι.z_mem ι.z_ne hgz
    have hyQ : y ∈ pCoreOf 2 (l32nH T V) := by
      have h := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ (inv_mem hgH)) r).mp
        ι.r_Q
      rw [inv_inv] at h
      exact h
    exact hyU (ι.mem_U_of_mem_L hyQ hyL)

theorem false : False := by
  have h13 := ι.ctx.hyp.hyp.h13
  have := h13.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTG := ι.ctx.hyp.fsu.sylow
  set P : Sylow 2 G := IsPGroup.toSylow hTG.1 hTG.2 with hPdef
  have hP : (P : Subgroup G) = T := IsPGroup.toSylow_coe hTG.1 hTG.2
  have key : commutator G ≠ ⊤ := by
    refine CFSG.RankThree.PartTwo.Sec8.commutator_ne_top_of_extremal P (N := L)
      (fun a ha b hb => ?_) (x := r) (by rw [hP]; exact ι.r_T) ι.r_notL
      (by rw [pow_two]; exact ι.r_sq)
      fun g hg => ?_
    · rw [hP] at ha hb
      exact ι.comm_mem ha hb
    · rw [hP] at hg
      have hyT : g⁻¹ * r * g ∈ T := hg r ⟨ι.r_T, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
      rw [ι.mul_mem_iff (inv_mem ι.r_T) hyT, inv_mem_iff]
      exact iff_of_false ι.r_notL (ι.conj_not_mem_L hg)
  apply key
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
  · exfalso
    obtain ⟨a', b', hab⟩ := h13.nonabelian
    have hmem : ⁅a', b'⁆ ∈ commutator G := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a') (Subgroup.mem_top b')
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hab hmem
  · exact h

end Inv

end L14333

open L14333 in
theorem lemma14333MEqL_of_inputs (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h1288 : Lemma12_8_8_two) (h12884 : Lemma12_8_8_four)
    (h12810 : Lemma12_8_10) (h12811 : Lemma12_8_11) (h12811h : Lemma12_8_11_hat)
    (h12812 : Lemma12_8_12_two) (h12813 : Lemma12_8_13) (h14323 : Lemma14323Rest)
    (h14324 : Lemma14324One) (h14331 : Lemma14331One) (hKG22 : KGG22PointStab)
    (hKGr : KGG22Rank) (hKGq : KGSp4Quad) (hKGl : KGSp4Line) (hKGL24 : KGL24Quad) :
    Lemma14333MEqL := by
  intro G _ _ T L V h hlt
  obtain ⟨V₂, K, g, a, z, b, d, x, D, c⟩ := exists_ctx h1332 h1334 h1222 h12213 h37 h38 h39
    h1288 h12810 h12811 h12811h h12812 h12813 h14323 h14324 h14331 hKG22 hKGr hKGq
    hKGl hKGL24 h hlt
  have hyp := (h12884 G T L V 3 (fsuV1 T V) V₂ c.ctx.setting le_rfl).2
  have hTS : QuasithinUnique.IsSylowTwoOf T (l32nH T V) :=
    h.isSylowTwoOf_l32nH (stmtL32NModule_of_inputs h1332 h1334)
  refine le_antisymm ?_ Subgroup.le_normalizer
  by_cases hcd : ∀ q ∈ pCoreOf 2 (l32nH T V), q * x = x * q → q * d = d * q
  · exact (c.normalizer_L_le hyp hTS).trans (sup_le le_rfl (c.le_L_of_comm_d hyp hTS hcd))
  · push Not at hcd
    obtain ⟨q, hq, hqx, hqd⟩ := hcd
    have hqd' : q * d * q⁻¹ = d⁻¹ := by
      refine (c.conj_d hyp (pCoreOf_le 2 _ hq)).resolve_left fun h' => hqd ?_
      calc q * d = q * d * q⁻¹ * q := by group
        _ = d * q := by rw [h']
    obtain ⟨r, hr, hrx, hrd, hrV, hrP, hrL, hrr⟩ := c.exists_inv hyp hq hqx hqd'
    exact (Inv.false ⟨c, hyp, hTS, hr, hrx, hrd, hrV, hrP, hrL, hrr⟩).elim

end CFSG.Quasithin.H13
