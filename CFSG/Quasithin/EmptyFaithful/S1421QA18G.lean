module

public import CFSG.Quasithin.EmptyFaithful.S1421L16
public import CFSG.Quasithin.EmptyFaithful.S1421STC2
public import CFSG.Quasithin.EmptyFaithful.S1421QA18Z

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1421QA18

variable {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_of_commute {Z : Subgroup G} {m : G} (hm : ∀ w ∈ Z, w * m = m * w) :
    m ∈ Subgroup.normalizer (Z : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  have h1 : ∀ w ∈ Z, m * w * m⁻¹ = w := fun w hw => by rw [← hm w hw]; group
  have h2 : ∀ w ∈ Z, m⁻¹ * w * m = w := fun w hw => by
    calc m⁻¹ * w * m = m⁻¹ * (w * m) := by group
      _ = m⁻¹ * (m * w) := by rw [hm w hw]
      _ = w := by group
  constructor
  · intro hg
    rw [h1 g hg]
    exact hg
  · intro hg
    have h3 := h2 _ hg
    have e : m⁻¹ * (m * g * m⁻¹) * m = g := by group
    rw [e] at h3
    rw [h3]
    exact hg

theorem charTwo_mcOf (h : Hyp1421 G T M) : CharTwo (mcOf T) := by
  obtain ⟨S, hS⟩ := h.toQTFE14.exists_sylow
  have hSM : (S : Subgroup G) ≤ mcOf T := hS ▸ h.toQTFE14.t_le_mc
  exact h.toQTFE14.qtke.2.1 (mcOf T) h.mc_max.1 ⟨S, hSM⟩

theorem omegaOneCenter_le_pCoreOf_mcOf (h : Hyp1421 G T M) :
    quasithinOmegaOneCenter T ≤ pCoreOf 2 (mcOf T) := by
  have hZT : quasithinOmegaOneCenter T ≤ T := fun g hg =>
    (quasithinOmegaOneCenter_le_center T hg).1
  refine le_pCoreOf_of_le_normalizer 2 (hZT.trans h.toQTFE14.t_le_mc) ?_ (h.sylow.1.to_le hZT)
  intro m hm
  exact mem_normalizer_of_commute fun w hw => Subgroup.mem_centralizer_iff.mp hm w hw

theorem eq_one_or_eq_of_card_two {Γ : Type} [Group Γ] (h : Nat.card Γ = 2) {a : Γ} (ha : a ≠ 1)
    (b : Γ) : b = 1 ∨ b = a := by
  obtain ⟨x, y, hxy, hxyu⟩ := Nat.card_eq_two_iff.mp h
  have hmem : ∀ g : Γ, g = x ∨ g = y := fun g => by
    have : g ∈ ({x, y} : Set Γ) := by rw [hxyu]; trivial
    simpa using this
  rcases hmem 1 with h1 | h1 <;> rcases hmem a with ha' | ha' <;> rcases hmem b with hb | hb
  · exact absurd (ha'.trans h1.symm) ha
  · exact absurd (ha'.trans h1.symm) ha
  · exact Or.inl (hb.trans h1.symm)
  · exact Or.inr (hb.trans ha'.symm)
  · exact Or.inr (hb.trans ha'.symm)
  · exact Or.inl (hb.trans h1.symm)
  · exact absurd (ha'.trans h1.symm) ha
  · exact absurd (ha'.trans h1.symm) ha

theorem eq_one_of_centralizes (st : Setting1427 T M H K1)
    (hQ : pCoreOf 2 (mcOf T) = pCoreOf 2 K1) (hsp : IsSpecialPow 2 2 4 ↥(pCoreOf 2 K1))
    {x : G} (hxMc : x ∈ mcOf T) (hxK : ∀ k ∈ K1, x * k * x⁻¹ = k)
    (hxL : ∀ l ∈ S1421.l2Of T H (yOfL22 T M), x * l * x⁻¹ = l) : x = 1 := by
  have hyp := st.hyp
  obtain ⟨z, hz2, hz1, hzT, hzZ, -, -, -, hZ⟩ := exists_z hyp
  have hQK : pCoreOf 2 K1 ≤ K1 := pCoreOf_le 2 K1
  have hK1Mc : K1 ≤ mcOf T := S1421.K1_le_mcOf st
  have hcomm : ∀ q ∈ pCoreOf 2 K1, x * q = q * x := fun q hq => by
    have := hxK q (hQK hq)
    calc x * q = x * q * x⁻¹ * x := by group
      _ = q * x := by rw [this]
  have hxQ : x ∈ pCoreOf 2 K1 := by
    have hxc : x ∈ Subgroup.centralizer (pCoreOf 2 (mcOf T) : Set G) := by
      rw [hQ, Subgroup.mem_centralizer_iff]
      intro w hw
      exact (hcomm w hw).symm
    have := charTwo_mcOf hyp ⟨hxMc, hxc⟩
    rwa [hQ] at this
  have hzQ : z ∈ pCoreOf 2 K1 := by
    rw [← hQ]
    exact omegaOneCenter_le_pCoreOf_mcOf hyp hzZ
  have hzcomm : ∀ q ∈ pCoreOf 2 K1, z * q = q * z := fun q hq =>
    Subgroup.mem_centralizer_iff.mp (hK1Mc (hQK hq)) z hzZ
  have hxc : (⟨x, hxQ⟩ : ↥(pCoreOf 2 K1)) ∈ Subgroup.center ↥(pCoreOf 2 K1) := by
    rw [Subgroup.mem_center_iff]
    intro q
    exact Subtype.ext (hcomm q.1 q.2).symm
  have hzc : (⟨z, hzQ⟩ : ↥(pCoreOf 2 K1)) ∈ Subgroup.center ↥(pCoreOf 2 K1) := by
    rw [Subgroup.mem_center_iff]
    intro q
    exact Subtype.ext (hzcomm q.1 q.2).symm
  have hne : (⟨⟨z, hzQ⟩, hzc⟩ : ↥(Subgroup.center ↥(pCoreOf 2 K1))) ≠ 1 := by
    intro h
    exact hz1 (congrArg (fun c : ↥(Subgroup.center ↥(pCoreOf 2 K1)) => ((c : ↥(pCoreOf 2 K1)) : G))
      h)
  rcases eq_one_or_eq_of_card_two hsp.2.2 hne ⟨⟨x, hxQ⟩, hxc⟩ with h | h
  · exact congrArg (fun c : ↥(Subgroup.center ↥(pCoreOf 2 K1)) => ((c : ↥(pCoreOf 2 K1)) : G)) h
  · exfalso
    have hxz : x = z := congrArg (fun c : ↥(Subgroup.center ↥(pCoreOf 2 K1)) =>
      ((c : ↥(pCoreOf 2 K1)) : G)) h
    subst hxz
    refine S1421.not_l2_le_normalizer_Z (H := H) hyp st.facts (fun l hl => ?_)
    refine mem_normalizer_of_commute fun w hw => ?_
    rcases hZ w hw with rfl | rfl
    · simp
    · have := hxL l hl
      calc w * l = w * l * w⁻¹ * w := by group
        _ = l * w := by rw [this]

theorem l2_inf_mcOf_le_s2 (h : Hyp1421 G T M) (F : Facts1422 T M) :
    S1421.l2Of T H (yOfL22 T M) ⊓ mcOf T ≤ S1421.s2Of T H (yOfL22 T M) := by
  rintro x ⟨hxL, hxMc⟩
  obtain ⟨y, hy, s, hs, rfl⟩ := (S1421.mem_l2_iff h).mp hxL
  have hsMc : s ∈ mcOf T := h.toQTFE14.t_le_mc (S1421.s2_le_T h hs)
  have hyMc : y ∈ mcOf T := by
    have := (mcOf T).mul_mem hxMc ((mcOf T).inv_mem hsMc)
    simpa using this
  have hO : pCoreOf 2 (yOfL22 T M) ≤ yOfL22 T M ⊓ mcOf T := by
    refine le_inf (pCoreOf_le 2 _) ?_
    have hy2 : pCoreOf 2 (yOfL22 T M) = yOfL22 T M ⊓ Subgroup.centralizer (VZ T M : Set G) :=
      F.y_oTwo
    rw [hy2]
    refine inf_le_right.trans (Subgroup.centralizer_le ?_)
    exact fun g hg => le_conjClosure _ _ hg
  have hidx := S1421.relIndex_pCoreOf_y h F
  have htower := Subgroup.relIndex_mul_relIndex (pCoreOf 2 (yOfL22 T M))
    (yOfL22 T M ⊓ mcOf T) (yOfL22 T M) hO inf_le_left
  rw [hidx] at htower
  have hdvd : (yOfL22 T M ⊓ mcOf T).relIndex (yOfL22 T M) ∣ 3 := Dvd.intro_left _ htower
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exfalso
    have hle : yOfL22 T M ≤ yOfL22 T M ⊓ mcOf T := Subgroup.relIndex_eq_one.mp h1
    refine S1421.not_y_le_normalizer_Z h F (fun g hg => ?_)
    exact mem_normalizer_of_commute fun w hw =>
      (Subgroup.mem_centralizer_iff.mp (hle hg).2 w hw)
  · rw [h3] at htower
    have h1 : (pCoreOf 2 (yOfL22 T M)).relIndex (yOfL22 T M ⊓ mcOf T) = 1 := by omega
    have hyO : y ∈ pCoreOf 2 (yOfL22 T M) := Subgroup.relIndex_eq_one.mp h1 ⟨hy, hyMc⟩
    exact (S1421.s2Of T H (yOfL22 T M)).mul_mem (Subgroup.mem_sup_left hyO) hs

theorem bigB_eq (h311 : Theorem311) (st : Setting1427 T M H K1)
    (h13 : pCoreOf 2 (yOfL22 T M) ≤ S1421.sOf T K1) (hS : S1421.sOf T K1 = T) (hTK : T ≤ K1) :
    bigB K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1) =
      K1 ⊓ Subgroup.normalizer (T : Set G) := by
  have hB2 := S1421.borelOf_l2_eq h311 st h13
  have hS₂T : S1421.s2Of T H (yOfL22 T M) ≤ T := S1421.s2_le_T st.hyp
  have hK : borelOf K1 (S1421.sOf T K1) = K1 ⊓ Subgroup.normalizer (T : Set G) := by
    unfold borelOf
    rw [hS, inf_eq_left.mpr hTK]
  have hTB : T ≤ K1 ⊓ Subgroup.normalizer (T : Set G) := le_inf hTK Subgroup.le_normalizer
  unfold bigB
  rw [hK, hB2, hS]
  exact le_antisymm (sup_le (sup_le le_rfl (hS₂T.trans hTB)) hTB) (le_sup_left.trans le_sup_left)

theorem sup_bigB_eq (h311 : Theorem311) (st : Setting1427 T M H K1)
    (h13 : pCoreOf 2 (yOfL22 T M) ≤ S1421.sOf T K1) (hS : S1421.sOf T K1 = T) (hTK : T ≤ K1) :
    K1 ⊔ bigB K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1) = K1 := by
  rw [bigB_eq h311 st h13 hS hTK]
  exact sup_eq_left.mpr inf_le_left

omit [Finite G] in
theorem le_normalizer_l2 (hK : oTwoUpper H = K1) {X : Subgroup G} (hXM : X ≤ M)
    (hXT : X ≤ Subgroup.normalizer (T : Set G)) (hXK : X ≤ Subgroup.normalizer (K1 : Set G)) :
    X ≤ Subgroup.normalizer (S1421.l2Of T H (yOfL22 T M) : Set G) := by
  have hXY : X ≤ Subgroup.normalizer (yOfL22 T M : Set G) :=
    hXM.trans (le_normalizer_yOfL22 T M)
  have hXO : X ≤ Subgroup.normalizer (pCoreOf 2 (yOfL22 T M) : Set G) :=
    F7.le_normalizer_pCoreOf_of_le_normalizer hXY
  have hXTK : X ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := by
    rw [hK]
    exact fun g hg => Subgroup.inf_normalizer_le_normalizer_inf ⟨hXT hg, hXK hg⟩
  exact F1.le_normalizer_sup hXY (F1.le_normalizer_sup hXO hXTK)

omit [Finite G] in
theorem le_normalizer_l2_sup (hK : oTwoUpper H = K1) {X : Subgroup G} (hXM : X ≤ M)
    (hXT : X ≤ Subgroup.normalizer (T : Set G)) (hXK : X ≤ Subgroup.normalizer (K1 : Set G)) :
    X ≤ Subgroup.normalizer
      ((S1421.l2Of T H (yOfL22 T M) ⊔ K1 ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) :
        Set G) := by
  have hXB : X ≤ Subgroup.normalizer ((K1 ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) :
      Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hXK hg, F1.mem_normalizer_normalizer (hXT hg)⟩
  exact F1.le_normalizer_sup (le_normalizer_l2 hK hXM hXT hXK) hXB

theorem l2_le_M (h : Hyp1421 G T M) : S1421.l2Of T H (yOfL22 T M) ≤ M :=
  sup_le (yOfL22_le T M) ((S1421.s2_le_T h).trans (S1421.T_le_M h))

theorem l2_sup_inf_mcOf_le (st : Setting1427 T M H K1) (hK : oTwoUpper H = K1) (hTK : T ≤ K1) :
    (S1421.l2Of T H (yOfL22 T M) ⊔ K1 ⊓ Subgroup.normalizer (T : Set G)) ⊓ mcOf T ≤ K1 := by
  have hyp := st.hyp
  have hBM : K1 ⊓ Subgroup.normalizer (T : Set G) ≤ M := by
    have hb := st.notation_.borel_le
    rw [inf_eq_left.mpr hTK] at hb
    exact hb
  have hBL : K1 ⊓ Subgroup.normalizer (T : Set G) ≤
      Subgroup.normalizer (S1421.l2Of T H (yOfL22 T M) : Set G) :=
    le_normalizer_l2 hK hBM inf_le_right (inf_le_left.trans Subgroup.le_normalizer)
  rintro x ⟨hxLB, hxMc⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hBL).mp hxLB
  have hbMc : b ∈ mcOf T := S1421.K1_le_mcOf st hb.1
  have haMc : a ∈ mcOf T := by
    have := (mcOf T).mul_mem hxMc ((mcOf T).inv_mem hbMc)
    simpa using this
  have haS : a ∈ S1421.s2Of T H (yOfL22 T M) := l2_inf_mcOf_le_s2 hyp st.facts ⟨ha, haMc⟩
  exact K1.mul_mem (hTK (S1421.s2_le_T hyp haS)) hb.1

end S1421QA18

end CFSG.Quasithin
