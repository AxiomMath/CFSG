module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2LocH

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

namespace InspW2

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t d x : G}

section Bw

variable (h : Ctx T M g A t d x)

include h in
theorem Bw_inf_Q_of_ctx :
    Bw T d x ⊓ qOf T ≤ Subgroup.zpowers (u0Of d x) ⊔ Subgroup.zpowers (wOfX d x) := by
  obtain ⟨d', hA⟩ := exists_q8Data_u0 h
  have hDU : dOf T M ≤ Subgroup.centralizer (uOfL22 T M : Set G) := inf_le_right
  rintro q ⟨hqB, hqQ⟩
  rw [h.c19.a.q_eq, sup_comm] at hqQ
  obtain ⟨δ, hδ, u, hu, rfl⟩ := CFSG.Quasithin.mem_sup_of_commute hDU hqQ
  have hcomm : ∀ v ∈ uOfL22 T M, v * u0Of d x = u0Of d x * v → u * v = v * u := by
    intro v hv hvu
    have h1 : v * (δ * u) = (δ * u) * v :=
      Subgroup.mem_centralizer_iff.mp hqB.2 v (mem_K0_of_mem_U_comm h hv hvu)
    have h2 : v * δ = δ * v := Subgroup.mem_centralizer_iff.mp (hDU hδ) v hv
    have h3 : δ * (v * u) = δ * (u * v) := by
      calc δ * (v * u) = (δ * v) * u := by rw [mul_assoc]
        _ = (v * δ) * u := by rw [h2]
        _ = v * (δ * u) := by rw [mul_assoc]
        _ = (δ * u) * v := h1
        _ = δ * (u * v) := by rw [mul_assoc]
    exact (mul_left_cancel h3).symm
  have huz : u ∈ Subgroup.zpowers (u0Of d x) :=
    mem_zpowers_u0_of_comm h hA hu (hcomm _ (u0Of_mem_U h.c h.c18 h.hD h.hd4 h.hx h.hx3 h.hΓ) rfl)
      (fun b hb => hcomm b b.2 (congrArg Subtype.val (d'.mul_comm_u0 hA hb)))
  have hdW : d ∈ Subgroup.zpowers (u0Of d x) ⊔ Subgroup.zpowers (wOfX d x) := by
    have h1 : wOfX d x * (u0Of d x)⁻¹ ∈
        Subgroup.zpowers (u0Of d x) ⊔ Subgroup.zpowers (wOfX d x) :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
        (Subgroup.inv_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)))
    have h2 : wOfX d x * (u0Of d x)⁻¹ = d := by rw [wOfX_eq_mul_u0Of]; group
    rwa [h2] at h1
  have hδW : δ ∈ Subgroup.zpowers (u0Of d x) ⊔ Subgroup.zpowers (wOfX d x) := by
    have : δ ∈ Subgroup.zpowers d := h.hD ▸ hδ
    exact (Subgroup.zpowers_le.mpr hdW) this
  exact Subgroup.mul_mem _ hδW (Subgroup.mem_sup_left huz)

include h in
theorem Bw_invol_of_ctx : ∀ b ∈ Bw T d x, b * b = 1 → b ∈ qOf T := by
  intro b hb hb2
  obtain ⟨d', hA⟩ := exists_q8Data_u0 h
  have hu₀U := u0Of_mem_U h.c h.c18 h.hD h.hd4 h.hx h.hx3 h.hΓ
  have hu₀z := u0Of_sq h.c h.hD h.hd4 h.hx h.hx3
  have hdd := dd_facts h.hd4
  have hzZ := sq_mem_omegaOneCenter h.c h.hD h.hd4
  have hbH : b ∈ mcOf T := hb.1.1
  set u₀ := u0Of d x with hu₀def
  have hbK : ∀ k ∈ K0 T d x, k * b = b * k := fun k hk =>
    Subgroup.mem_centralizer_iff.mp hb.2 k hk
  have hfix : ∀ v ∈ uOfL22 T M, v * u₀ = u₀ * v → b * v * b⁻¹ = v := by
    intro v hv hvu
    have h1 := hbK v (mem_K0_of_mem_U_comm h hv hvu)
    calc b * v * b⁻¹ = (v * b) * b⁻¹ := by rw [h1]
      _ = v := by group
  have hbU : ∀ y ∈ uOfL22 T M, b * y * b⁻¹ ∈ uOfL22 T M := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (h.c.hHU hbH) y).mp hy
  have hZc : ∀ z' ∈ quasithinOmegaOneCenter T, ∀ y ∈ uOfL22 T M, y * z' = z' * y := by
    intro z' hz' y hy
    have hz'U : z' ∈ centerOf (uOfL22 T M) := by rw [h.c.centerOf_uOfL22_eq]; exact hz'
    exact Subgroup.mem_centralizer_iff.mp hz'U.2 y hy
  have hcommZ : ∀ y ∈ uOfL22 T M, y * u₀ * y⁻¹ * u₀⁻¹ ∈ quasithinOmegaOneCenter T := by
    intro y hy
    rw [← h.c.centerOf_uOfL22_eq]
    exact isQ8Sq_comm_mem_centerOf h.c.c15.q8sq y hy u₀ hu₀U
  have hall : ∀ u ∈ uOfL22 T M, b * u * b⁻¹ * u⁻¹ ∈ quasithinOmegaOneCenter T := by
    intro u hu
    have ha : b * u * b⁻¹ ∈ uOfL22 T M := hbU u hu
    have hc' : u⁻¹ * (b * u * b⁻¹) ∈ uOfL22 T M :=
      (uOfL22 T M).mul_mem ((uOfL22 T M).inv_mem hu) ha
    have hcomm' : ∀ v ∈ uOfL22 T M, v * u₀ = u₀ * v →
        (u * v * u⁻¹) * u₀ = u₀ * (u * v * u⁻¹) →
        (u⁻¹ * (b * u * b⁻¹)) * v = v * (u⁻¹ * (b * u * b⁻¹)) := by
      intro v hv hvu hv'u
      have hv' : u * v * u⁻¹ ∈ uOfL22 T M :=
        (uOfL22 T M).mul_mem ((uOfL22 T M).mul_mem hu hv) ((uOfL22 T M).inv_mem hu)
      have h1 := hfix _ hv' hv'u
      have h2 := hfix v hv hvu
      have e1 : (b * u * b⁻¹) * v * (b * u * b⁻¹)⁻¹ = u * v * u⁻¹ := by
        calc (b * u * b⁻¹) * v * (b * u * b⁻¹)⁻¹
            = (b * u * b⁻¹) * (b * v * b⁻¹) * (b * u * b⁻¹)⁻¹ := by rw [h2]
          _ = b * (u * v * u⁻¹) * b⁻¹ := by group
          _ = u * v * u⁻¹ := h1
      calc (u⁻¹ * (b * u * b⁻¹)) * v
          = u⁻¹ * (((b * u * b⁻¹) * v * (b * u * b⁻¹)⁻¹) * (b * u * b⁻¹)) := by group
        _ = u⁻¹ * ((u * v * u⁻¹) * (b * u * b⁻¹)) := by rw [e1]
        _ = v * (u⁻¹ * (b * u * b⁻¹)) := by group
    have hu₀' : (u * u₀ * u⁻¹) * u₀ = u₀ * (u * u₀ * u⁻¹) := by
      have hz' := hZc _ (hcommZ u hu) u₀ hu₀U
      have e : u * u₀ * u⁻¹ = (u * u₀ * u⁻¹ * u₀⁻¹) * u₀ := by group
      calc (u * u₀ * u⁻¹) * u₀ = ((u * u₀ * u⁻¹ * u₀⁻¹) * u₀) * u₀ := by rw [← e]
        _ = (u₀ * (u * u₀ * u⁻¹ * u₀⁻¹)) * u₀ := by rw [← hz']
        _ = u₀ * ((u * u₀ * u⁻¹ * u₀⁻¹) * u₀) := by rw [mul_assoc]
        _ = u₀ * (u * u₀ * u⁻¹) := by rw [← e]
    have hcu := hcomm' u₀ hu₀U rfl hu₀'
    have hcB : ∀ b₀ : ↥(uOfL22 T M), b₀ ∈ d'.B →
        (u⁻¹ * (b * u * b⁻¹)) * (b₀ : G) = (b₀ : G) * (u⁻¹ * (b * u * b⁻¹)) := by
      intro b₀ hb₀
      refine hcomm' b₀ b₀.2 (congrArg Subtype.val (d'.mul_comm_u0 hA hb₀)) ?_
      have hmem : (⟨u, hu⟩ * b₀ * ⟨u, hu⟩⁻¹ : ↥(uOfL22 T M)) ∈ d'.B :=
        d'.normal_B.conj_mem b₀ hb₀ ⟨u, hu⟩
      exact congrArg Subtype.val (d'.mul_comm_u0 hA hmem)
    have hc'z := mem_zpowers_u0_of_comm h hA hc' hcu hcB
    obtain ⟨c', hc'def⟩ : ∃ c', c' = u⁻¹ * (b * u * b⁻¹) := ⟨_, rfl⟩
    rw [← hc'def] at hc' hcu hc'z
    have hx : b * u * b⁻¹ = u * c' := by rw [hc'def]; group
    have hbc' : b * c' * b⁻¹ = c' := hfix c' hc' hcu
    have hcc : c' * c' = 1 := by
      have e2 : b * (b * u * b⁻¹) * b⁻¹ = u := by
        calc b * (b * u * b⁻¹) * b⁻¹ = (b * b) * u * (b * b)⁻¹ := by group
          _ = u := by rw [hb2]; group
      have e3 : b * (b * u * b⁻¹) * b⁻¹ = u * (c' * c') := by
        calc b * (b * u * b⁻¹) * b⁻¹ = b * (u * c') * b⁻¹ := by rw [← hx]
          _ = (b * u * b⁻¹) * (b * c' * b⁻¹) := by group
          _ = (u * c') * c' := by rw [hbc', ← hx]
          _ = u * (c' * c') := by rw [mul_assoc]
      exact mul_left_cancel (e3.symm.trans (e2.trans (mul_one u).symm))
    have hc'Z : c' ∈ quasithinOmegaOneCenter T := by
      rcases mem_zpowers_four hu₀z hdd.1 hc'z with h1 | h1 | h1 | h1
      · rw [h1]; exact (quasithinOmegaOneCenter T).one_mem
      · exfalso; rw [h1, hu₀z] at hcc; exact hdd.2 hcc
      · rw [h1]; exact hzZ
      · exfalso
        rw [h1, ← hu₀z] at hcc
        apply hdd.2
        have hzz' : (u₀ * u₀) * (u₀ * u₀) = 1 := by rw [hu₀z]; exact hdd.1
        rw [← hu₀z]
        calc u₀ * u₀ = (u₀ * u₀) * ((u₀ * u₀) * (u₀ * u₀)) := by rw [hzz', mul_one]
          _ = (u₀ * (u₀ * u₀)) * (u₀ * (u₀ * u₀)) := by simp only [mul_assoc]
          _ = 1 := hcc
    have hfin : b * u * b⁻¹ * u⁻¹ = c' := by
      calc b * u * b⁻¹ * u⁻¹ = u * c' * u⁻¹ := by rw [hx]
        _ = c' * u * u⁻¹ := by rw [hZc c' hc'Z u hu]
        _ = c' := by group
    rw [hfin]
    exact hc'Z
  have hone : h.c.actK ⟨b, hbH⟩ = 1 :=
    (actTilde_eq_one_iff (quasithinOmegaOneCenter T) (uOfL22 T M) (mcOf T) (hHN_of T)
      h.c.hHU h.c.hUN ⟨b, hbH⟩).mpr hall
  exact h.c.mem_qOf_of_actK_eq_one hone

end Bw

end InspW2

end S143

end CFSG.Quasithin
