module

public import CFSG.LocalAnalysis.WeakClosure81.W18Asch66
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6Gen
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6OddTr

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch1413

open CFSG.Quasithin CFSG.Open Subgroup

open scoped commutatorElement

private theorem a1413CaseI_comm {G : Type*} [Group G] {A : Subgroup G}
    (hA : IsMulCommutative A) {x y : G} (hx : x ∈ A) (hy : y ∈ A) : x * y = y * x :=
  congrArg Subtype.val (hA.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

private theorem a1413CaseI_conj_zpow_eq {G : Type*} [Group G] {x t : G}
    (h : x * t = t * x) (n : ℤ) : x * t ^ n * x⁻¹ = t ^ n := by
  have hconj : MulAut.conj x t = t := by rw [MulAut.conj_apply, h]; group
  calc x * t ^ n * x⁻¹ = (MulAut.conj x) (t ^ n) := by rw [← MulAut.conj_apply]
    _ = ((MulAut.conj x) t) ^ n := by rw [map_zpow]
    _ = t ^ n := by rw [hconj]

private theorem a1413CaseI_isQuadratic_map {Q V : Type} [Group Q] [CommGroup V]
    {ρ : Q →* MulAut V} {A : Subgroup Q} (hq : IsQuadraticOn ρ A) :
    IsQuadratic (A.map ρ) := by
  rw [IsQuadratic, FixVLat.commV_le_iff]
  intro x hx v
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
  rw [mem_fixV]
  intro y hy
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hy
  exact hq b hb c hc v

theorem asch1413_caseI_false {Q : Type} [Group Q] [Finite Q] {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {ρ : Q →* MulAut V} (hρ : Function.Injective ρ)
    {L A X : Subgroup Q} {z : Q} (hLn : L.Normal)
    (hC : ∀ v : V, (∀ l ∈ L, ρ l v = v) → v = 1)
    (hA : Nat.card A = 4) (hAe : IsElemAbelian 2 A) (hq : IsQuadraticOn ρ A)
    (hzA : z ∈ A) (hz2 : orderOf z = 2) (hzL : z ∈ L)
    (hXL : X ≤ L) (hXz : X ≤ centralizer ({z} : Set Q)) (hXperf : ⁅X, X⁆ = X)
    (hCX : ∀ y : Q, (∀ x ∈ X, y * x = x * y) → y ∈ zpowers z)
    (hnorm : ∀ N : Subgroup Q, N ≤ L → N ≤ centralizer ({z} : Set Q) →
      (∀ c ∈ L, c * z = z * c → ∀ n ∈ N, c * n * c⁻¹ ∈ N) → z ∈ N → ¬ N ≤ zpowers z → X ≤ N)
    (hgen : ∀ h ∈ L, h * z * h⁻¹ ≠ z → (h * z * h⁻¹) * z = z * (h * z * h⁻¹) →
      L ≤ X ⊔ X.map (MulAut.conj h).toMonoidHom)
    (hbad : ∃ g ∈ L, Even (orderOf (z * (g * z * g⁻¹))) ∧ 2 < orderOf (z * (g * z * g⁻¹))) :
    False := by
  classical
  obtain ⟨g0, hg0L, hg0even, hg0gt⟩ := hbad
  set a : MulAut V := ρ z with ha_def
  set Cz : Subgroup Q := Subgroup.centralizer ({z} : Set Q) with hCz_def
  have hCz_mem : ∀ x : Q, x ∈ Cz ↔ z * x = x * z := by
    intro x
    rw [hCz_def, Subgroup.mem_centralizer_iff]
    exact ⟨fun h => h z (Set.mem_singleton z), fun h w hw => by
      rw [Set.mem_singleton_iff] at hw; subst hw; exact h⟩
  have hACz : A ≤ Cz := by
    intro u hu
    exact (hCz_mem u).mpr (a1413CaseI_comm hAe.1 hzA hu)
  have hCz_conj_mem : ∀ c ∈ Cz, ∀ u ∈ Cz, c * u * c⁻¹ ∈ Cz := by
    intro c hc u hu
    simp only [hCz_mem] at hc hu ⊢
    have hconjz : MulAut.conj c z = z := by rw [MulAut.conj_apply, ← hc]; group
    have h := congrArg (MulAut.conj c) hu
    rw [map_mul, map_mul, hconjz] at h
    simpa [MulAut.conj_apply] using h
  set B : Subgroup Q :=
    Subgroup.closure {b : Q | ∃ c ∈ Cz, b ∈ A.map (MulAut.conj c).toMonoidHom} with hB_def
  have hAleB : A ≤ B := by
    rw [hB_def]
    intro u hu
    exact Subgroup.subset_closure ⟨1, (hCz_mem 1).mpr (by simp), by
      exact Subgroup.mem_map.mpr ⟨u, hu, by simp [MulAut.conj_apply]⟩⟩
  have hBleCz : B ≤ Cz := by
    rw [hB_def]
    refine (Subgroup.closure_le Cz).mpr ?_
    rintro b ⟨c, hc, hbc⟩
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hbc
    exact hCz_conj_mem c hc u (hACz hu)
  have hBnorm : ∀ c ∈ Cz, B.map (MulAut.conj c).toMonoidHom ≤ B := by
    intro c hc
    rw [Subgroup.map_le_iff_le_comap]
    intro b hb
    rw [Subgroup.mem_comap]
    rw [hB_def] at hb
    induction hb using Subgroup.closure_induction with
    | mem b hbS =>
        obtain ⟨c', hc', hbc'⟩ := hbS
        obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hbc'
        have hcc' : c * c' ∈ Cz := Cz.mul_mem hc hc'
        change (MulAut.conj c) ((MulAut.conj c') u) ∈ B
        have heq : (MulAut.conj c) ((MulAut.conj c') u) =
            (MulAut.conj (c * c')) u := by
          simp only [MulAut.conj_apply]; group
        rw [heq]
        exact Subgroup.subset_closure ⟨c * c', hcc', Subgroup.mem_map.mpr ⟨u, hu, rfl⟩⟩
    | one => rw [map_one]; exact B.one_mem
    | mul x y _ _ ihx ihy => rw [map_mul]; exact B.mul_mem ihx ihy
    | inv x _ ihx => rw [map_inv]; exact B.inv_mem ihx
  have hBQY : B ≤ (Asch6.quadY ρ.range (A.map ρ) a).comap ρ := by
    intro b hb
    rw [Subgroup.mem_comap]
    rw [hB_def] at hb
    induction hb using Subgroup.closure_induction with
    | mem b hbS =>
        obtain ⟨c, hc, hbc⟩ := hbS
        obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hbc
        have hca : ρ c * a = a * ρ c := by
          have hcz : z * c = c * z := (hCz_mem c).mp hc
          rw [ha_def]
          calc ρ c * ρ z = ρ (c * z) := by rw [map_mul]
            _ = ρ (z * c) := by rw [hcz]
            _ = ρ z * ρ c := by rw [map_mul]
        have heq : ρ ((MulAut.conj c).toMonoidHom u) =
            (MulAut.conj (ρ c)).toMonoidHom (ρ u) := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
        rw [heq]
        refine Subgroup.mem_iSup_of_mem (ρ c) (Subgroup.mem_iSup_of_mem ⟨c, rfl⟩
          (Subgroup.mem_iSup_of_mem hca ?_))
        exact Subgroup.mem_map.mpr ⟨ρ u, Subgroup.mem_map.mpr ⟨u, hu, rfl⟩, rfl⟩
    | one => rw [map_one]; exact (Asch6.quadY ρ.range (A.map ρ) a).one_mem
    | mul x y _ _ ihx ihy =>
        rw [map_mul]; exact (Asch6.quadY ρ.range (A.map ρ) a).mul_mem ihx ihy
    | inv x _ ihx => rw [map_inv]; exact (Asch6.quadY ρ.range (A.map ρ) a).inv_mem ihx
  have hquad : IsQuadratic (A.map ρ) := a1413CaseI_isQuadratic_map hq
  have haA' : a ∈ A.map ρ := by
    rw [ha_def]; exact Subgroup.mem_map.mpr ⟨z, hzA, rfl⟩
  have hBfix : ∀ y ∈ B.map ρ, ∀ w ∈ commV (Subgroup.zpowers a), y w = w := by
    intro y hy w hw
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    have hbQ : ρ b ∈ Asch6.quadY ρ.range (A.map ρ) a := Subgroup.mem_comap.mp (hBQY hb)
    exact Asch6.fixes_commV_quadY (G := ρ.range) (A := A.map ρ) hquad haA' (ρ b) hbQ w hw
  have hnotN : ¬ B ⊓ L ≤ Subgroup.zpowers z := by
    intro hNle
    have hBX_le : ⁅B, X⁆ ≤ B ⊓ L := by
      rw [Subgroup.commutator_le]
      intro b hb x hx
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have hxb : x * b * x⁻¹ ∈ B := by
          have := hBnorm x (hXz hx) (Subgroup.mem_map.mpr ⟨b, hb, rfl⟩)
          simpa [MulAut.conj_apply] using this
        have heq : ⁅b, x⁆ = b * (x * b * x⁻¹)⁻¹ := by
          rw [commutatorElement_def]; group
        rw [heq]
        exact B.mul_mem hb (B.inv_mem hxb)
      · have hxL : x ∈ L := hXL hx
        have h1 : b * x * b⁻¹ ∈ L := hLn.conj_mem x hxL b
        have heq : ⁅b, x⁆ = (b * x * b⁻¹) * x⁻¹ := by
          rw [commutatorElement_def]
        rw [heq]
        exact L.mul_mem h1 (L.inv_mem hxL)
    have hBX_z : ⁅B, X⁆ ≤ Subgroup.zpowers z := le_trans hBX_le hNle
    have hXB_z : ⁅X, B⁆ ≤ Subgroup.zpowers z := by
      rw [Subgroup.commutator_comm]; exact hBX_z
    have key : ∀ S T : Subgroup Q, ⁅S, T⁆ ≤ Subgroup.zpowers z → ⁅⁅S, T⁆, X⁆ = ⊥ := by
      intro S T hS
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro w hw y hy
      have hwz : w ∈ Subgroup.zpowers z := hS hw
      have hyz : y * z = z * y := ((hCz_mem y).mp (hXz hy)).symm
      have hyw : y * w = w * y := by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hwz
        have h1 := a1413CaseI_conj_zpow_eq (x := y) (t := z) hyz n
        calc y * z ^ n = (y * z ^ n * y⁻¹) * y := by group
          _ = z ^ n * y := by rw [h1]
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hyw.symm
    have h1 : ⁅⁅X, B⁆, X⁆ = ⊥ := key X B hXB_z
    have h2 : ⁅⁅B, X⁆, X⁆ = ⊥ := key B X hBX_z
    have hXB_bot : ⁅X, B⁆ = ⊥ := by
      have hrot := Subgroup.commutator_commutator_eq_bot_of_rotate
        (H₁ := X) (H₂ := X) (H₃ := B) h1 h2
      rwa [hXperf] at hrot
    have hBz : B ≤ Subgroup.zpowers z := by
      intro b hb
      refine hCX b ?_
      intro x hx
      exact (Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hXB_bot hx)) b hb
    have hAz : A ≤ Subgroup.zpowers z := le_trans hAleB hBz
    have hcard := Subgroup.card_le_of_le hAz
    rw [Nat.card_zpowers, hz2] at hcard
    omega
  have hNnorm : ∀ c ∈ L, c * z = z * c → ∀ n ∈ B ⊓ L, c * n * c⁻¹ ∈ B ⊓ L := by
    intro c hcL hcz n hn
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hcCz : c ∈ Cz := (hCz_mem c).mpr hcz.symm
      have := hBnorm c hcCz (Subgroup.mem_map.mpr ⟨n, hn.1, rfl⟩)
      simpa [MulAut.conj_apply] using this
    · exact hLn.conj_mem n hn.2 c
  have hXN : X ≤ B ⊓ L :=
    hnorm (B ⊓ L) inf_le_right (le_trans inf_le_left hBleCz) hNnorm
      (Subgroup.mem_inf.mpr ⟨hAleB hzA, hzL⟩) hnotN
  have hXB : X ≤ B := le_trans hXN inf_le_left
  have hYfix : ∀ y ∈ X.map ρ, ∀ w ∈ commV (Subgroup.zpowers a), y w = w := by
    intro y hy w hw
    exact hBfix y (Subgroup.map_mono (f := ρ) hXB hy) w hw
  have hLbot : fixV (L.map ρ) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro v hv
    exact hC v (fun l hl => (mem_fixV.mp hv) (ρ l) (Subgroup.mem_map.mpr ⟨l, hl, rfl⟩))
  have hdisj : ∀ h' ∈ L.map ρ, h' * a * h'⁻¹ * a = a * (h' * a * h'⁻¹) →
      h' * a * h'⁻¹ ≠ a →
      commV (Subgroup.zpowers a) ⊓ commV (Subgroup.zpowers (h' * a * h'⁻¹)) = ⊥ := by
    intro h' hh' hcomm hne
    obtain ⟨h, hhL, rfl⟩ := Subgroup.mem_map.mp hh'
    have hzhcomm : (h * z * h⁻¹) * z = z * (h * z * h⁻¹) := by
      apply hρ
      simpa only [map_mul, map_inv, ← ha_def] using hcomm
    have hzhne : h * z * h⁻¹ ≠ z := by
      intro heq
      apply hne
      calc ρ h * a * (ρ h)⁻¹ = ρ (h * z * h⁻¹) := by
            rw [ha_def, map_mul, map_mul, map_inv]
        _ = ρ z := by rw [heq]
        _ = a := ha_def.symm
    have hhgen : L ≤ X ⊔ X.map (MulAut.conj h).toMonoidHom := hgen h hhL hzhne hzhcomm
    have hcomp : (MulAut.conj (ρ h)).toMonoidHom.comp ρ =
        ρ.comp (MulAut.conj h).toMonoidHom := by
      apply MonoidHom.ext
      intro x
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
      apply MulEquiv.ext
      intro v
      show (MulAut.conj (ρ h) (ρ x)) v = (ρ (MulAut.conj h x)) v
      rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
    have hYmap : (X.map (MulAut.conj h).toMonoidHom).map ρ =
        (X.map ρ).map (MulAut.conj (ρ h)).toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map, hcomp]
    have hLle : L.map ρ ≤ (X.map ρ) ⊔ (X.map ρ).map (MulAut.conj (ρ h)).toMonoidHom := by
      have h : L.map ρ ≤ (X ⊔ X.map (MulAut.conj h).toMonoidHom).map ρ :=
        Subgroup.map_mono (f := ρ) hhgen
      rwa [Subgroup.map_sup, hYmap] at h
    have hgen' : fixV ((X.map ρ) ⊔ (X.map ρ).map (MulAut.conj (ρ h)).toMonoidHom) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro v hv
      have hv' : v ∈ fixV (L.map ρ) := fun x hx => (mem_fixV.mp hv) x (hLle hx)
      rw [hLbot] at hv'
      simpa using hv'
    have hres := Asch6.commV_inf_commV_conj_eq_bot (Y := X.map ρ) (a := a) (h := ρ h)
      hYfix hgen'
    simpa only [MulAut.conj_apply] using hres
  have hzsq : z ^ 2 = 1 := by simpa [hz2] using pow_orderOf_eq_one z
  have ha2 : a ^ 2 = 1 := by rw [ha_def, ← map_pow, hzsq, map_one]
  have haG : a ∈ L.map ρ := by
    rw [ha_def]; exact Subgroup.mem_map.mpr ⟨z, hzL, rfl⟩
  have hgG : ρ g0 ∈ L.map ρ := Subgroup.mem_map.mpr ⟨g0, hg0L, rfl⟩
  have hres := Asch6.odd_or_le_two_of_inf_commV_eq_bot (V := V) hV haG ha2 hdisj hgG
  have hzgg : a * (ρ g0 * a * (ρ g0)⁻¹) = ρ (z * (g0 * z * g0⁻¹)) := by
    simp only [ha_def, map_mul, map_inv]
  have hord : orderOf (a * (ρ g0 * a * (ρ g0)⁻¹)) =
      orderOf (z * (g0 * z * g0⁻¹)) := by
    rw [hzgg, orderOf_injective ρ hρ]
  rcases hres with hodd | hle
  · rw [hord] at hodd
    exact (Nat.not_odd_iff_even.mpr hg0even) hodd
  · rw [hord] at hle
    omega

end CFSG.LocalAnalysis.WeakClosure81.Asch1413

end
